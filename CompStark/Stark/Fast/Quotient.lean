/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Openings

/-! # The fast quotient is the specification's

The fast quotient works in the extension's stored, bit-reversed row order. Stored row `j` is the
quotient domain's natural row `perm[j]`; the trace there is the extension's row `j`, because the
bit reversal is an involution (`bitRevPerm_getD_getD`). Its next row is stored at `next[j]`, and
its selectors and inverse vanishing polynomial are the specification's at `perm[j]`. So every
block of stored rows holds the specification's rows `quotientRow … perm[j]`, and reordering by
`perm` puts row `r` in place.
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial

open Montgomery.Native32

section
variable {F : Type} [BaseField F]

theorem rowAcc_cons (a : Expr F × List F) (cw : List (Expr F × List F)) (ev : Expr F → F) (j : Nat)
    (x : F) : rowAcc (a :: cw) ev j x = rowAcc cw ev j (x + ev a.1 * a.2.getD j 0) := by
  rw [rowAcc, rowAcc, List.foldl_cons]

/-- The rows `perm[0], perm[1], …` of a matrix. -/
theorem permuteRows_eq (m : Mat F) (perm : Array Nat) : permuteRows m perm =
    Array.ofFn (n := perm.size * m.width) fun k ↦
      m.values.getD (perm.getD (k.val / m.width) 0 * m.width + k.val % m.width) 0 := by
  simp only [permuteRows, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl, pure_bind, bind_pure,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← Array.foldl_toList]
  have : perm.toList = (List.range' 0 perm.size).map (perm.getD · 0) := by
    apply List.ext_getElem (by simp only [Array.length_toList, List.length_map, List.length_range'])
    intro i h1 h2
    rw [Array.length_toList] at h1
    rw [Array.getElem_toList, List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some]
  rw [this, List.foldl_map, CompStark.Stark.foldl_blocks, Array.emptyWithCapacity_eq,
    Array.empty_append]
  simp only [Nat.zero_add]
  rfl

/-- Entry `(r, c)` of the rows `perm[0], perm[1], …`. -/
theorem permuteRows_getD (m : Mat F) (perm : Array Nat) (r c : Nat) (hr : r < perm.size)
    (hc : c < m.width) : (permuteRows m perm).getD (r * m.width + c) 0 =
      m.values.getD (perm.getD r 0 * m.width + c) 0 := by
  have hlt : r * m.width + c < perm.size * m.width := by
    have : (r + 1) * m.width ≤ perm.size * m.width := Nat.mul_le_mul_right _ hr
    rw [Nat.succ_mul] at this
    omega
  rw [permuteRows_eq, NTTFast.Packed.getD_ofFn_bounded _ _ hlt]
  have hd : (r * m.width + c) / m.width = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]
  have hm : (r * m.width + c) % m.width = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp only [hd, hm]

theorem getD_map_lt {α β : Type} (a : Array α) (f : α → β) (j : Nat) (h : j < a.size) (d : β)
    (d' : α) : (a.map f).getD j d = f (a.getD j d') := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h,
    Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h,
    Option.getD_some]

end

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p

/-! ### The bit-reversal permutation -/

theorem bitRevPerm_getD_lt (b i : Nat) (hi : i < 2 ^ b) : (bitRevPerm b).getD i 0 < 2 ^ b := by
  rw [bitRevPerm_getD b i hi]
  exact NTT.Transform.bitRevNat_lt b i

/-- `bitRevPerm` is an involution. -/
theorem bitRevPerm_getD_getD (b i : Nat) (hi : i < 2 ^ b) :
    (bitRevPerm b).getD ((bitRevPerm b).getD i 0) 0 = i := by
  rw [bitRevPerm_getD b _ (bitRevPerm_getD_lt b i hi), bitRevPerm_getD b i hi,
    NTT.Transform.bitRevNat_involutive b i hi]

/-! ### Parallel ranges of blocks -/

/-- Ranges of blocks of `B` entries, concatenated in order, give the whole. -/
theorem parChunks_eq_blocks {α : Type} (n parts B : Nat) (f : Nat → Nat → Array α) (g : Nat → α)
    (hf : ∀ s len, s + len ≤ n ∨ len = 0 →
      f s len = Array.ofFn (n := len * B) fun k ↦ g (s * B + k.val))
    (hp : 0 < parts ∨ n = 0) :
    parChunks n parts f = Array.ofFn (n := n * B) fun i ↦ g i.val := by
  unfold parChunks
  generalize hsz : (n + parts - 1) / parts = size
  have hstep : ∀ k, ((List.range k).foldl (fun acc i ↦ acc ++
      f (i * size) (min size (n - min n (i * size)))) #[]).toList =
      (List.range (min n (k * size) * B)).map g := by
    intro k
    induction k with
    | zero => rw [List.range_zero, List.foldl_nil, Nat.zero_mul, Nat.min_zero, Nat.zero_mul]; rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.toList_append,
        ih, hf _ _ (by omega), toList_ofFn_eq_map (fun x ↦ g (k * size * B + x))]
      by_cases hk : k * size ≤ n
      · rw [show min n ((k + 1) * size) * B = min n (k * size) * B +
            min size (n - min n (k * size)) * B by
            rw [← Nat.add_mul]; congr 1; rw [Nat.succ_mul]; omega,
          List.range_add, List.map_append, List.map_map, Nat.min_eq_right hk]
        rfl
      · rw [show min size (n - min n (k * size)) = 0 by omega,
          show min n ((k + 1) * size) = min n (k * size) by rw [Nat.succ_mul]; omega,
          Nat.zero_mul, List.range_zero, List.map_nil, List.append_nil]
  have hn : min n (parts * size) = n := by
    rcases hp with hp | hp
    · have := Nat.lt_div_mul_add (a := n + parts - 1) hp
      rw [hsz] at this
      rw [Nat.min_eq_left (by rw [Nat.mul_comm]; omega)]
    · rw [hp, Nat.zero_min]
  apply Array.toList_inj.mp
  rw [toList_ofFn_eq_map, Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
  have := hstep parts
  rw [hn] at this
  exact this

/-! ### The transposed trace -/

/-- The first `parts · R` rows of the row-major `vals` of width `w`, as `parts` pieces of `R` rows,
every piece column-major. -/
def colsOf (vals : Array F) (w parts R : Nat) : Array F :=
  Array.ofFn (n := parts * (w * R)) fun m ↦
    vals.getD ((m.val / (w * R) * R + m.val % (w * R) % R) * w + m.val % (w * R) / R) 0

/-- The pieces `quotientWith` transposes, concatenated, are `colsOf`. -/
theorem pieces_eq (vals : Array F) (w parts R : Nat) (hM : parts * R * w ≤ vals.size)
    (hs : 4 * vals.size < USize.size) :
    ((Array.range parts).map fun k ↦ Task.spawn fun _ ↦
        NTTFast.Packed.Native.transposeRows (encode vals) w (k * R) R).foldl
      (fun acc t ↦ acc ++ t.get) ByteArray.empty = encode (colsOf vals w parts R) := by
  rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
  let g (m : Nat) : F := vals.getD ((m / (w * R) * R + m % (w * R) % R) * w + m % (w * R) / R) 0
  suffices h : ∀ pr ≤ parts, (List.range pr).foldl (fun acc k ↦ acc ++
      (Task.spawn fun _ ↦ NTTFast.Packed.Native.transposeRows (encode vals) w (k * R) R).get)
      ByteArray.empty = encode (Array.ofFn (n := pr * (w * R)) fun m ↦ g m.val) from
    h parts (Nat.le_refl _)
  intro pr hp
  induction pr with
  | zero => rw [List.range_zero, List.foldl_nil, Nat.zero_mul]; rfl
  | succ pr ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
    have hle : (pr * R + R) * w ≤ vals.size := by
      refine le_trans (Nat.mul_le_mul_right w ?_) hM
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right R hp
    show _ ++ NTTFast.Packed.Native.transposeRows (encode vals) w (pr * R) R = _
    rw [transposeRows_encode _ _ _ _ hle hs, Nat.succ_mul, ← ofFn_append_ofFn,
      CompPoly.PackedRepr.encode_append]
    congr 2
    apply Array.ext (by rw [Array.size_ofFn, Array.size_ofFn])
    intro k h1 h2
    rw [Array.size_ofFn] at h1
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    have hL : 0 < w * R := by omega
    have hd : (pr * (w * R) + k) / (w * R) = pr := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt h1, Nat.zero_add]
    have hm : (pr * (w * R) + k) % (w * R) = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
    simp only [g, hd, hm]

/-- The cell of column `c < w` at row `j` is the trace's. -/
theorem colsOf_cell (vals : Array F) (w parts R c j : Nat) (hc : c < w) (hj : j < parts * R) :
    (colsOf vals w parts R).getD (j / R * (R * w) + c * R + j % R) 0 = vals.getD (j * w + c) 0 := by
  have hR : 0 < R := Nat.pos_of_ne_zero fun h ↦ by rw [h, Nat.mul_zero] at hj; omega
  have hjR : j / R < parts := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
  have hin : c * R + j % R < w * R := by
    have := Nat.mod_lt j hR
    have : (c + 1) * R ≤ w * R := Nat.mul_le_mul_right R hc
    rw [Nat.succ_mul] at this
    omega
  have hm : j / R * (R * w) + c * R + j % R = j / R * (w * R) + (c * R + j % R) := by
    rw [Nat.mul_comm R w, Nat.add_assoc]
  have hlt : j / R * (w * R) + (c * R + j % R) < parts * (w * R) := by
    have : (j / R + 1) * (w * R) ≤ parts * (w * R) := Nat.mul_le_mul_right _ hjR
    rw [Nat.succ_mul] at this
    omega
  rw [hm, colsOf, Words.getD_ofFn (parts * (w * R)) (fun m ↦
    vals.getD ((m / (w * R) * R + m % (w * R) % R) * w + m % (w * R) / R) 0),
    ite_eq_left_of_eq_true _ _ (eq_true hlt)]
  have hd : (j / R * (w * R) + (c * R + j % R)) / (w * R) = j / R := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hin, Nat.zero_add]
  have hmod : (j / R * (w * R) + (c * R + j % R)) % (w * R) = c * R + j % R := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  have h1 : (c * R + j % R) % R = j % R := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  have h2 : (c * R + j % R) / R = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt (Nat.mod_lt j hR),
      Nat.zero_add]
  rw [hd, hmod, h1, h2, Nat.div_add_mod' j R]

/-- Words `i, …, i + B - 1` of an encoded array. -/
theorem slice_encode_ofFn (a : Array F) (i B : Nat) (h : i + B ≤ a.size) :
    slice (encode a) i B = encode (Array.ofFn (n := B) fun k ↦ a.getD (i + k.val) 0) := by
  rw [slice_encode]
  congr 1
  apply Array.ext (by rw [Array.size_extract, Array.size_ofFn]; omega)
  intro k h1 h2
  rw [Array.getElem_extract, Array.getElem_ofFn, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by omega), Option.getD_some]

/-- A block of `B` rows, `B` dividing the piece height `R` and `r0`, lies in one piece. -/
theorem block_in_piece (B R r0 k : Nat) (hR : 0 < R) (hB : B ∣ R) (hr : B ∣ r0) (hk : k < B) :
    (r0 + k) / R = r0 / R ∧ (r0 + k) % R = r0 % R + k := by
  have hm : B ∣ r0 % R := (Nat.dvd_mod_iff hB).mpr hr
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hB
  have hlt : r0 % R < R := Nat.mod_lt r0 hR
  have hab : a + 1 ≤ b := by
    rw [ha, hb] at hlt
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega
  have hle : r0 % R + B ≤ R := by
    rw [ha, hb, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left B hab
  have hsplit : r0 + k = (r0 % R + k) + R * (r0 / R) := by
    have := Nat.mod_add_div r0 R
    omega
  constructor
  · rw [hsplit, Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Gathered words are the encoded array's at the gathered cells. -/
theorem gather_encode (C : Array F) (w R c : Nat) (idx : Array Nat) (r0 B : Nat)
    (hs : 4 * C.size < USize.size) (hB : 4 * B < USize.size)
    (hi : ∀ k < B, idx.getD (r0 + k) 0 / R * (R * w) + c * R + idx.getD (r0 + k) 0 % R < C.size) :
    gather (encode C) w R c idx r0 B = encode (Array.ofFn (n := B) fun k ↦
      C.getD (idx.getD (r0 + k.val) 0 / R * (R * w) + c * R + idx.getD (r0 + k.val) 0 % R) 0) := by
  let f (k : Nat) : F :=
    C.getD (idx.getD (r0 + k) 0 / R * (R * w) + c * R + idx.getD (r0 + k) 0 % R) 0
  unfold gather
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    bind_pure, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  rw [Words.zeroWords_eq (p := p), ← Words.upto_zero (Array.replicate B 0) f, List.range_eq_range',
    Words.foldl_tail _ _ _ _ _ (fun k _ hk ↦ by
      rw [cell, Words.read_encode C _ hs (hi k (by omega))]
      exact Words.write_upto _ f k (by rw [Array.size_replicate]; omega)
        (by rw [Array.size_replicate]; omega)),
    Nat.zero_add, Words.upto_full _ _ _ (Array.size_replicate ..)]

theorem cell_lt (w parts R c j : Nat) (hc : c < w) (hj : j < parts * R) :
    j / R * (R * w) + c * R + j % R < parts * (w * R) := by
  have hR : 0 < R := Nat.pos_of_ne_zero fun h ↦ by rw [h, Nat.mul_zero] at hj; omega
  have hjR : j / R < parts := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
  have hin : c * R + j % R < w * R := by
    have := Nat.mod_lt j hR
    have : (c + 1) * R ≤ w * R := Nat.mul_le_mul_right R hc
    rw [Nat.succ_mul] at this
    omega
  have : (j / R + 1) * (w * R) ≤ parts * (w * R) := Nat.mul_le_mul_right _ hjR
  rw [Nat.succ_mul, Nat.mul_comm R w] at *
  omega

/-- A slice of column `c < w` over a block of `B` stored rows from `r0` is the trace's column
there. -/
theorem slice_cols (vals : Array F) (w parts R B c r0 : Nat) (hc : c < w) (hR : 0 < R)
    (hBR : B ∣ R) (hBr : B ∣ r0) (hB0 : 0 < B) (hr : r0 + B ≤ parts * R) :
    slice (encode (colsOf vals w parts R)) (r0 / R * (R * w) + c * R + r0 % R) B =
      encode (Array.ofFn (n := B) fun k ↦ vals.getD ((r0 + k.val) * w + c) 0) := by
  have hcell (k : Nat) (hk : k < B) : r0 / R * (R * w) + c * R + r0 % R + k =
      (r0 + k) / R * (R * w) + c * R + (r0 + k) % R := by
    obtain ⟨h1, h2⟩ := block_in_piece B R r0 k hR hBR hBr hk
    rw [h1, h2, Nat.add_assoc]
  have hlast := cell_lt w parts R c (r0 + (B - 1)) hc (by omega)
  rw [← hcell (B - 1) (by omega)] at hlast
  rw [slice_encode_ofFn _ _ _ (by rw [colsOf, Array.size_ofFn]; omega)]
  congr 1
  apply Array.ext (by rw [Array.size_ofFn, Array.size_ofFn])
  intro k h1 h2
  rw [Array.size_ofFn] at h1
  rw [Array.getElem_ofFn, Array.getElem_ofFn, hcell k h1,
    colsOf_cell vals w parts R c (r0 + k) hc (by omega)]

/-- A block of `B` stored rows from `r0` of the next rows of column `c`, as `evalWords` reads
it: the values `g` there. -/
theorem nextWords_eq (vals : Array F) (w parts R B : Nat) (next : Array Nat)
    (contiguous : Array (Option Nat)) (r0 c : Nat) (hc : c < w) (hR : 0 < R) (hBR : B ∣ R)
    (hB0 : 0 < B) (hr : r0 + B ≤ parts * R) (hsC : 4 * (colsOf vals w parts R).size < USize.size)
    (hBs : 4 * B < USize.size) (hnext : ∀ j < parts * R, next.getD j 0 < parts * R)
    (hcont : ∀ n0, contiguous.getD (r0 / B) none = some n0 →
      B ∣ n0 ∧ ∀ k < B, next.getD (r0 + k) 0 = n0 + k)
    (g : Nat → F) (hg : ∀ j < parts * R, g j = vals.getD (next.getD j 0 * w + c) 0) :
    (match contiguous.getD (r0 / B) none with
      | some n0 => slice (encode (colsOf vals w parts R)) (n0 / R * (R * w) + c * R + n0 % R) B
      | none => gather (encode (colsOf vals w parts R)) w R c next r0 B) =
      encode (Array.ofFn (n := B) fun k ↦ g (r0 + k.val)) := by
  split
  · rename_i n0 hn0
    obtain ⟨hdvd, hk⟩ := hcont n0 hn0
    have hn0lt : n0 < parts * R := by
      have h0 := hk 0 hB0
      rw [Nat.add_zero, Nat.add_zero] at h0
      rw [← h0]
      exact hnext r0 (by omega)
    have hn0B : n0 + B ≤ parts * R := by
      obtain ⟨a, ha⟩ := hdvd
      obtain ⟨b, hb⟩ := Nat.dvd_trans hBR (Dvd.intro_left parts rfl)
      rw [ha] at hn0lt ⊢
      rw [hb] at hn0lt ⊢
      have := Nat.lt_of_mul_lt_mul_left hn0lt
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left B this
    rw [slice_cols vals w parts R B c n0 hc hR hBR hdvd hB0 hn0B]
    congr 1
    refine congrArg Array.ofFn (funext fun k ↦ ?_)
    rw [hg _ (by omega), hk k.val k.isLt]
  · rw [gather_encode _ _ _ _ _ _ _ hsC (by omega) (fun k hk ↦ by
      rw [colsOf, Array.size_ofFn]
      exact cell_lt w parts R c _ hc (hnext _ (by omega)))]
    congr 1
    refine congrArg Array.ofFn (funext fun k ↦ ?_)
    rw [colsOf_cell vals w parts R c _ hc (hnext _ (by omega)), hg _ (by omega)]

theorem size_colsOf (vals : Array F) (w parts R : Nat) (hv : parts * R * w ≤ vals.size)
    (hs : 4 * vals.size < USize.size) : 4 * (colsOf vals w parts R).size < USize.size := by
  rw [colsOf, Array.size_ofFn]
  have : parts * (w * R) ≤ vals.size := by rw [← Nat.mul_assoc, Nat.mul_right_comm]; exact hv
  omega

/-- `evalWords` on a block of `B` stored rows from `r0` is the expression at those rows, for
expressions on the columns of the trace `vals` and the preprocessed trace `pvals`, with the `np`
periodic columns of `n` rows each in `perVals`. `E j` is the environment of stored row `j`. -/
theorem evalWords_eq (vals pvals perVals : Array F) (w pw np n parts R B : Nat)
    (next : Array Nat)
    (contiguous : Array (Option Nat)) (pis : List F) (fA lA tA : Array F) (r0 : Nat)
    (E : Nat → Expr.Env F F) (hR : 0 < R) (hBR : B ∣ R) (hB0 : 0 < B) (hBr : B ∣ r0)
    (hr : r0 + B ≤ parts * R) (hv : parts * R * w ≤ vals.size) (hs : 4 * vals.size < USize.size)
    (hpv : parts * R * pw ≤ pvals.size) (hps : 4 * pvals.size < USize.size)
    (hpn : np * n ≤ perVals.size) (hrn : r0 + B ≤ n)
    (hBs : 4 * B < USize.size) (hnext : ∀ j < parts * R, next.getD j 0 < parts * R)
    (hcont : ∀ n0, contiguous.getD (r0 / B) none = some n0 →
      B ∣ n0 ∧ ∀ k < B, next.getD (r0 + k) 0 = n0 + k)
    (hf : r0 + B ≤ fA.size) (hl : r0 + B ≤ lA.size) (ht : r0 + B ≤ tA.size)
    (hEcur : ∀ j < parts * R, ∀ c < w, (E j).cur c = vals.getD (j * w + c) 0)
    (hEnext : ∀ j < parts * R, ∀ c < w, (E j).next c = vals.getD (next.getD j 0 * w + c) 0)
    (hEpcur : ∀ j < parts * R, ∀ c < pw, (E j).prepCur c = pvals.getD (j * pw + c) 0)
    (hEpnext : ∀ j < parts * R, ∀ c < pw,
      (E j).prepNext c = pvals.getD (next.getD j 0 * pw + c) 0)
    (hEper : ∀ j < parts * R, ∀ c,
      (E j).periodic c = if c < np then perVals.getD (c * n + j) 0 else 0)
    (hEpub : ∀ j i, (E j).pub i = pis.getD i 0) (hEconst : ∀ j x, (E j).const x = x)
    (hEf : ∀ j < parts * R, (E j).isFirstRow = fA.getD j 0)
    (hEl : ∀ j < parts * R, (E j).isLastRow = lA.getD j 0)
    (hEt : ∀ j < parts * R, (E j).isTransition = tA.getD j 0) :
    ∀ e : Expr F, e.colsBelow w w pw pw = true →
      evalWords (encode (colsOf vals w parts R)) (encode (colsOf pvals pw parts R))
        (encode perVals) w pw np n R B next contiguous pis (encode fA) (encode lA) (encode tA) r0
        e =
      encode (Array.ofFn (n := B) fun k ↦ e.eval (E (r0 + k.val))) := by
  have hsC := size_colsOf vals w parts R hv hs
  have hpsC := size_colsOf pvals pw parts R hpv hps
  have hsel (X : Array F) (hX : r0 + B ≤ X.size) (g : Nat → F)
      (hg : ∀ j < parts * R, g j = X.getD j 0) :
      slice (encode X) r0 B = encode (Array.ofFn (n := B) fun k ↦ g (r0 + k.val)) := by
    rw [slice_encode_ofFn X r0 B hX]
    exact congrArg encode (congrArg Array.ofFn (funext fun k ↦ (hg _ (by omega)).symm))
  intro e he
  induction e with
  | cur c =>
    simp only [Expr.colsBelow, decide_eq_true_eq] at he
    rw [evalWords, slice_cols vals w parts R B c r0 he hR hBR hBr hB0 hr]
    congr 1
    refine congrArg Array.ofFn (funext fun k ↦ ?_)
    rw [Expr.eval, hEcur _ (by omega) c he]
  | next c =>
    simp only [Expr.colsBelow, decide_eq_true_eq] at he
    rw [evalWords]
    exact nextWords_eq vals w parts R B next contiguous r0 c he hR hBR hB0 hr hsC hBs hnext hcont
      _ fun j hj ↦ hEnext j hj c he
  | prepCur c =>
    simp only [Expr.colsBelow, decide_eq_true_eq] at he
    rw [evalWords, slice_cols pvals pw parts R B c r0 he hR hBR hBr hB0 hr]
    congr 1
    refine congrArg Array.ofFn (funext fun k ↦ ?_)
    rw [Expr.eval, hEpcur _ (by omega) c he]
  | prepNext c =>
    simp only [Expr.colsBelow, decide_eq_true_eq] at he
    rw [evalWords]
    exact nextWords_eq pvals pw parts R B next contiguous r0 c he hR hBR hB0 hr hpsC hBs hnext
      hcont _ fun j hj ↦ hEpnext j hj c he
  | periodic c =>
    rw [evalWords]
    split
    · rename_i hc
      have h1 := Nat.mul_le_mul_right n (hc : c + 1 ≤ np)
      rw [Nat.succ_mul] at h1
      rw [slice_encode_ofFn perVals (c * n + r0) B (by omega)]
      congr 1
      refine congrArg Array.ofFn (funext fun k ↦ ?_)
      rw [Expr.eval, hEper _ (by omega) c, ite_eq_left hc, Nat.add_assoc]
    · rename_i hc
      rw [EVec.zeroWords_ofFn (p := p)]
      congr 1
      refine congrArg Array.ofFn (funext fun k ↦ ?_)
      rw [Expr.eval, hEper _ (by omega) c, ite_eq_right hc]
  | pub i =>
    rw [evalWords, Words.replicateWord_encode _ _ hBs]
    congr 1
    apply Array.ext (by rw [Array.size_replicate, Array.size_ofFn])
    intro k _ _
    rw [Array.getElem_replicate, Array.getElem_ofFn, Expr.eval, hEpub]
  | const x =>
    rw [evalWords, Words.replicateWord_encode _ _ hBs]
    congr 1
    apply Array.ext (by rw [Array.size_replicate, Array.size_ofFn])
    intro k _ _
    rw [Array.getElem_replicate, Array.getElem_ofFn, Expr.eval, hEconst]
  | isFirstRow => exact hsel fA hf _ hEf
  | isLastRow => exact hsel lA hl _ hEl
  | isTransition => exact hsel tA ht _ hEt
  | add a b iha ihb =>
    simp only [Expr.colsBelow, Bool.and_eq_true] at he
    rw [evalWords, iha he.1, ihb he.2, Words.addWords_encode _ _ _ (by rw [Array.size_ofFn])
      (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn]; omega) (by rw [Array.size_ofFn]; omega)]
    congr 1
    refine congrArg Array.ofFn (funext fun i ↦ ?_)
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt, NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt]
    rfl
  | sub a b iha ihb =>
    simp only [Expr.colsBelow, Bool.and_eq_true] at he
    rw [evalWords, iha he.1, ihb he.2, Words.subWords_encode _ _ _ (by rw [Array.size_ofFn])
      (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn]; omega) (by rw [Array.size_ofFn]; omega)]
    congr 1
    refine congrArg Array.ofFn (funext fun i ↦ ?_)
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt, NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt]
    rfl
  | mul a b iha ihb =>
    simp only [Expr.colsBelow, Bool.and_eq_true] at he
    rw [evalWords, iha he.1, ihb he.2, Words.mulWords_encode _ _ _ (by rw [Array.size_ofFn])
      (by rw [Array.size_ofFn]) (by rw [Array.size_ofFn]; omega) (by rw [Array.size_ofFn]; omega)]
    congr 1
    refine congrArg Array.ofFn (funext fun i ↦ ?_)
    rw [NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt, NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt]
    rfl

/-! ### Accumulating the weighted constraints -/

/-- The fast accumulation of weighted constraints over a block of `B` rows: entry `i` of plane `j`
is `rowAcc` at that row, from `X j i`. -/
theorem accWords [Mont32BaseField p] (B : Nat) (hB : 4 * B < USize.size) (V : Expr F → ByteArray)
    (ev : Expr F → Nat → F) :
    ∀ (cw : List (Expr F × List F)),
      (∀ a ∈ cw, V a.1 = encode (Array.ofFn (n := B) fun i ↦ ev a.1 i.val)) →
      (∀ a ∈ cw, a.2.length = 4) → ∀ (X : Nat → Nat → F),
      (cw.map fun a ↦ (a.1, a.2.map Subtype.val)).foldl (fun b a ↦
          (b.zip a.2.toArray).map fun x ↦ Words.mulAddWords p x.1 (V a.1) x.2 B)
        #[encode (Array.ofFn (n := B) fun i ↦ X 0 i.val),
          encode (Array.ofFn (n := B) fun i ↦ X 1 i.val),
          encode (Array.ofFn (n := B) fun i ↦ X 2 i.val),
          encode (Array.ofFn (n := B) fun i ↦ X 3 i.val)] =
      #[encode (Array.ofFn (n := B) fun i ↦ rowAcc cw (fun c ↦ ev c i.val) 0 (X 0 i.val)),
        encode (Array.ofFn (n := B) fun i ↦ rowAcc cw (fun c ↦ ev c i.val) 1 (X 1 i.val)),
        encode (Array.ofFn (n := B) fun i ↦ rowAcc cw (fun c ↦ ev c i.val) 2 (X 2 i.val)),
        encode (Array.ofFn (n := B) fun i ↦ rowAcc cw (fun c ↦ ev c i.val) 3 (X 3 i.val))]
  | [], _, _, X => rfl
  | (c, ws) :: cw, hV, hw, X => by
    obtain ⟨w0, w1, w2, w3, rfl⟩ : ∃ w0 w1 w2 w3, ws = [w0, w1, w2, w3] := by
      have h4 := hw (c, ws) List.mem_cons_self
      match ws, h4 with
      | [w0, w1, w2, w3], _ => exact ⟨w0, w1, w2, w3, rfl⟩
    have hc := hV (c, [w0, w1, w2, w3]) List.mem_cons_self
    have hs (j : Nat) : 4 * (Array.ofFn (n := B) fun i ↦ X j i.val).size < USize.size := by
      rw [Array.size_ofFn]; exact hB
    have hsv : 4 * (Array.ofFn (n := B) fun i ↦ ev c i.val).size < USize.size := by
      rw [Array.size_ofFn]; exact hB
    have hstep (j : Nat) (x : F) :
        Words.mulAddWords p (encode (Array.ofFn (n := B) fun i ↦ X j i.val)) (V c) x.val B =
          encode (Array.ofFn (n := B) fun i ↦ X j i.val + ev c i.val * x) := by
      rw [hc, Words.mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn])
        (by rw [Array.size_ofFn]) (hs j) hsv]
      congr 1
      refine congrArg Array.ofFn (funext fun i ↦ ?_)
      rw [NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt, NTTFast.Packed.getD_ofFn_bounded _ _ i.isLt]
    rw [List.map_cons, List.foldl_cons]
    have hinit : ((#[encode (Array.ofFn (n := B) fun i ↦ X 0 i.val),
          encode (Array.ofFn (n := B) fun i ↦ X 1 i.val),
          encode (Array.ofFn (n := B) fun i ↦ X 2 i.val),
          encode (Array.ofFn (n := B) fun i ↦ X 3 i.val)] : Array ByteArray).zip
          ([w0, w1, w2, w3].map Subtype.val).toArray).map
          (fun x ↦ Words.mulAddWords p x.1 (V c) x.2 B) =
        #[encode (Array.ofFn (n := B) fun i ↦ X 0 i.val + ev c i.val * [w0, w1, w2, w3].getD 0 0),
          encode (Array.ofFn (n := B) fun i ↦ X 1 i.val + ev c i.val * [w0, w1, w2, w3].getD 1 0),
          encode (Array.ofFn (n := B) fun i ↦ X 2 i.val + ev c i.val * [w0, w1, w2, w3].getD 2 0),
          encode (Array.ofFn (n := B) fun i ↦ X 3 i.val + ev c i.val * [w0, w1, w2, w3].getD 3 0)]
        := by
      simp only [List.map_cons, List.map_nil, List.zip_toArray, List.zip_cons_cons,
        List.zip_nil_left, List.map_toArray]
      rw [hstep, hstep, hstep, hstep]
      rfl
    rw [hinit]
    simp only [rowAcc_cons]
    exact accWords B hB V ev cw (fun a ha ↦ hV a (List.mem_cons_of_mem _ ha))
      (fun a ha ↦ hw a (List.mem_cons_of_mem _ ha))
      (fun j i ↦ X j i + ev c i * [w0, w1, w2, w3].getD j 0)

/-! ### The specification's trace and the tables -/

theorem lt_of_mem_bitRevPerm {b i : Nat} (h : i ∈ bitRevPerm b) : i < 2 ^ b := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp h
  have := bitRevPerm_getD_lt b j (by rw [← size_bitRevPerm b]; exact hj)
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some] at this

/-- A table of the selector values `sel` in stored order. -/
theorem table_encode (d l : Nat) (sel : Array F) (f : Nat → F)
    (hf : ∀ i < 2 ^ (d + l), f i = sel.getD i 0) :
    NTTFast.Packed.Native.encodeFields ((bitRevPerm (d + l)).map f) =
      encode ((bitRevPerm (d + l)).map fun i ↦ sel.getD i 0) := by
  rw [NTTFast.Packed.Native.encodeFields_eq]
  exact congrArg encode (Array.map_congr_left fun i hi ↦ hf i (lt_of_mem_bitRevPerm hi))

theorem tables_first [Mont32BaseField p] (d l : Nat) : (quotientTables (p := p) d l).first =
    encode ((bitRevPerm (d + l)).map fun i ↦ (qFirst d l : Array F).getD i 0) :=
  table_encode d l _ _ fun i hi ↦ by unfold qFirst; rw [NTTFast.Packed.getD_ofFn_bounded _ i hi]

theorem tables_last [Mont32BaseField p] (d l : Nat) : (quotientTables (p := p) d l).last =
    encode ((bitRevPerm (d + l)).map fun i ↦ (qLast d l : Array F).getD i 0) :=
  table_encode d l _ _ fun i hi ↦ by unfold qLast; rw [NTTFast.Packed.getD_ofFn_bounded _ i hi]

theorem tables_trans [Mont32BaseField p] (d l : Nat) : (quotientTables (p := p) d l).trans =
    encode ((bitRevPerm (d + l)).map fun i ↦ (qTrans d l : Array F).getD i 0) :=
  table_encode d l _ _ fun i hi ↦ (getD_map_lt (cosetPoints (gen : F) (d + l))
    (· - (twoAdicGen d)⁻¹) i (by rw [size_cosetPoints]; exact hi) 0 0).symm

/-- When a block's next rows are flagged contiguous, they are the block from the flagged row. -/
theorem contiguous_spec (next : Array Nat) (B m b n0 : Nat)
    (h : ((Array.range m).map fun b ↦
      if next.getD (b * B) 0 % B == 0 &&
          (List.range B).all (fun k ↦ next.getD (b * B + k) 0 == next.getD (b * B) 0 + k) then
        some (next.getD (b * B) 0) else none).getD b none = some n0) :
    B ∣ n0 ∧ ∀ k < B, next.getD (b * B + k) 0 = n0 + k := by
  by_cases hb : b < m
  · have hrb : (Array.range m).getD b 0 = b := by
      rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by rw [Array.size_range]; exact hb),
        Option.getD_some, Array.getElem_range]
    rw [getD_map_lt _ _ b (by rw [Array.size_range]; exact hb) none 0, hrb] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
      exact ⟨Nat.dvd_of_mod_eq_zero hc.1, fun k hk ↦ hc.2 k hk⟩
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
      (by rw [Array.size_map, Array.size_range]; omega), Option.getD_none] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

theorem tables_contiguous [Mont32BaseField p] (d l b n0 : Nat)
    (h : (quotientTables (p := p) d l).contiguous.getD b none = some n0) :
    (quotientTables (p := p) d l).B ∣ n0 ∧ ∀ k < (quotientTables (p := p) d l).B,
      (quotientTables (p := p) d l).next.getD
          (b * (quotientTables (p := p) d l).B + k) 0 = n0 + k :=
  contiguous_spec _ _ _ b n0 h

theorem tables_next [Mont32BaseField p] (d l j : Nat) (hj : j < 2 ^ (d + l)) :
    (quotientTables (p := p) d l).next.getD j 0 =
      (bitRevPerm (d + l)).getD (((bitRevPerm (d + l)).getD j 0 + 2 ^ l) % 2 ^ (d + l)) 0 :=
  getD_map_lt _ _ j (by rw [size_bitRevPerm]; exact hj) 0 0

/-! ### The quotient law -/

theorem getElem!_lit4
    (a b c d : ByteArray) : #[a, b, c, d][0]! = a ∧ #[a, b, c, d][1]! = b ∧ #[a, b, c,
        d][2]! = c ∧ #[a, b, c, d][3]! = d := ⟨rfl, rfl, rfl, rfl⟩

theorem word_encode_ofFn (B : Nat) (hB : 4 * B < USize.size) (X : Nat → F) (k : Nat)
    (hk : k < B) : word (encode (Array.ofFn (n := B) fun i ↦ X i.val)) k = X k := by
  rw [word, Words.read_encode _ _ (by rw [Array.size_ofFn]; exact hB)
      (by rw [Array.size_ofFn]; exact hk),
    NTTFast.Packed.ofWord_val, NTTFast.Packed.getD_ofFn_bounded _ _ hk]

/-- The preprocessed trace the quotient reads: the one given, or none of `height` rows. -/
abbrev prepOrEmpty (ps : Option (Mat F)) (height : Nat) : Mat F := ps.getD ⟨0, height, #[]⟩

theorem transposePieces_rel {m : PMat} {s : Mat F} (h : RM m s) (parts R : Nat)
    (hM : parts * R * s.width ≤ s.values.size) (hs : 4 * s.values.size < USize.size) :
    transposePieces m parts R = encode (colsOf s.values s.width parts R) := by
  obtain ⟨hw, -, hv⟩ := h
  unfold transposePieces
  rw [hv, hw]
  exact pieces_eq s.values s.width parts R hM hs

/-- The fast quotient is the specification's on related extensions of the trace and the
preprocessed trace. -/
theorem quotientWith_rel [Mont32BaseField p] [Binomial4 p] (A : Air F) (pis : List F) (d l : Nat)
    (alpha : EF) {ext : PMat} {s : Mat F} {prep : Option PMat} {ps : Option (Mat F)}
    (h : RM ext s) (hs : MatOk s) (hh : 2 ^ (d + l) ≤ s.height) (hp : Option.Rel RM prep ps)
    (hps : ∀ q ∈ ps, MatOk q ∧ q.height = s.height)
    (hc : ∀ c ∈ A.constraints, c.colsBelow s.width s.width ((ps.map (·.width)).getD 0)
      ((ps.map (·.width)).getD 0)) :
    quotientWith (quotientTables
        (p := p) d l) A pis ext prep alpha = quotientOfLde A pis d l s ps alpha := by
  have hRM := h
  obtain ⟨hw, hhe, hv⟩ := h
  obtain ⟨-, -, hvs', hadd⟩ := hs
  have hus : 4 * s.values.size < USize.size := by
    unfold Addressable at hadd
    rw [hvs']
    omega
  have hpw : (ps.map (·.width)).getD 0 = (prepOrEmpty ps s.height).width := by cases ps <;> rfl
  have hpw' : (prep.map (·.width)).getD 0 = (prepOrEmpty ps s.height).width := by
    cases hp with
    | none => rfl
    | @some a q hr => exact hr.1
  have hspv : (prepOrEmpty ps s.height).values.size =
      (prepOrEmpty ps s.height).width * s.height := by
    cases hp with
    | none => show (#[] : Array F).size = 0 * s.height; rw [Nat.zero_mul]; rfl
    | @some a q hr =>
      obtain ⟨⟨-, -, hq, -⟩, hqh⟩ := hps q rfl
      show q.values.size = q.width * s.height
      rw [hq, hqh]
  have husp : 4 * (prepOrEmpty ps s.height).values.size < USize.size := by
    cases hp with
    | none => show 4 * 0 < USize.size; have := USize.le_size; omega
    | @some a q hr =>
      obtain ⟨⟨-, -, hq, hqa⟩, -⟩ := hps q rfl
      unfold Addressable at hqa
      show 4 * q.values.size < USize.size
      rw [hq]
      omega
  have hpcols (parts R : Nat)
      (hM : parts * R * (prepOrEmpty ps s.height).width ≤
        (prepOrEmpty ps s.height).values.size) :
      (prep.map (transposePieces · parts R)).getD ByteArray.empty =
        encode (colsOf (prepOrEmpty ps s.height).values (prepOrEmpty ps s.height).width parts
          R) := by
    cases hp with
    | none =>
      show ByteArray.empty = encode (colsOf #[] 0 parts R)
      rw [Array.eq_empty_of_size_eq_zero (xs := colsOf _ _ _ _)
        (by rw [colsOf, Array.size_ofFn, Nat.zero_mul, Nat.mul_zero])]
      rfl
    | @some a q hr => exact transposePieces_rel hr parts R hM husp
  have hpq : (ps.map fun m ↦ Mat.ofValues m.width (2 ^ (d + l))
        (permuteRows m (bitRevPerm (d + l)))).getD (Mat.ofValues 0 (2 ^ (d + l)) #[]) =
      Mat.ofValues (prepOrEmpty ps s.height).width (2 ^ (d + l))
        (permuteRows (prepOrEmpty ps s.height) (bitRevPerm (d + l))) := by
    cases ps with
    | none =>
      show Mat.ofValues 0 (2 ^ (d + l)) #[] = Mat.ofValues 0 (2 ^ (d + l)) (permuteRows _ _)
      rw [Array.eq_empty_of_size_eq_zero (xs := permuteRows _ _)
        (by rw [permuteRows_eq, Array.size_ofFn]; rfl)]
    | some q => rfl
  generalize prepOrEmpty ps s.height = sp at hpw hpw' hspv husp hpcols hpq
  rw [hpw] at hc
  have hn' := hh
  unfold quotientWith
  have hTd : (quotientTables (p := p) d l).degreeBits = d := rfl
  have hTl : (quotientTables (p := p) d l).logChunks = l := rfl
  have hTp : (quotientTables (p := p) d l).perm = bitRevPerm (d + l) := rfl
  have hTz : (quotientTables (p := p) d l).invZh = batchInv (qZh d l) := rfl
  have hTB : (quotientTables (p := p) d l).B =
      min (2 ^ (d + l) / (if 2 ^ (d + l) < 4096 then 1 else 16)) 256 := rfl
  have hcont := tables_contiguous (p := p) d l
  have hnext := tables_next (p := p) d l
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [hTd, hTl, hTp, hTz, tables_first, tables_last, tables_trans] at *
  rw [hv, hw] at *
  generalize quotientTables (p := p) d l = T at hcont hnext hTB ⊢
  have hpow : ∃ e, 2 ^ (d + l) / (if 2 ^ (d + l) < 4096 then 1 else 16) = 2 ^ e ∧
      (if 2 ^ (d + l) < 4096 then 1 else 16) * 2 ^ e = 2 ^ (d + l) := by
    split
    · exact ⟨d + l, Nat.div_one _, Nat.one_mul _⟩
    · rename_i hge
      have h12 : 12 ≤ d + l := by
        by_contra hc
        exact hge (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega : d + l < 12))
          (le_refl _))
      have h16 : 2 ^ (d + l) = 16 * 2 ^ (d + l - 4) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add]
        congr 1
        omega
      refine ⟨d + l - 4, ?_, h16.symm⟩
      rw [h16, Nat.mul_div_cancel_left _ (by decide)]
  generalize (if 2 ^ (d + l) < 4096 then 1 else 16) = parts at hpow hTB ⊢
  obtain ⟨e, hRe, hpe⟩ := hpow
  rw [hRe] at hTB ⊢
  generalize T.B = B at hcont hTB ⊢
  have hparts : 0 < parts := Nat.pos_of_ne_zero fun h0 ↦ by
    rw [h0, Nat.zero_mul] at hpe; exact absurd hpe (Nat.two_pow_pos _).ne
  have hB0 : 0 < B := by rw [hTB]; exact Nat.lt_min.mpr ⟨Nat.two_pow_pos _, by decide⟩
  have hB256 : B ≤ 256 := by rw [hTB]; exact Nat.min_le_right _ _
  have hBR : B ∣ 2 ^ e := by
    rw [hTB]
    by_cases h8 : e ≤ 8
    · rw [Nat.min_eq_left (le_trans (Nat.pow_le_pow_right (by decide) h8) (le_refl (2 ^ 8)))]
    · rw [Nat.min_eq_right
        (le_trans (le_refl (2 ^ 8)) (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact Nat.pow_dvd_pow 2 (by omega)
  have hBn : B ∣ 2 ^ (d + l) := by rw [← hpe]; exact Dvd.dvd.mul_left hBR parts
  have hM : parts * 2 ^ e * s.width ≤ s.values.size := by
    rw [hpe, hvs', Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hn'
  have hMp : parts * 2 ^ e * sp.width ≤ sp.values.size := by
    rw [hpe, hspv, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hn'
  rw [transposePieces_rel hRM parts (2 ^ e) hM hus, hpcols parts (2 ^ e) hMp, hpw',
    NTTFast.Packed.Native.encodeFields_eq]
  unfold quotientOfLde
  dsimp only
  rw [hpq, quotientValues_eq]
  generalize A.periodic.map (fun col ↦ periodicOnQuotient col d l) = pl
  obtain ⟨perVals, hPV⟩ : ∃ v, v = Array.ofFn (n := pl.toArray.size * 2 ^ (d + l)) fun k ↦
      periodicRow (pl.toArray.getD (k.val / 2 ^ (d + l)) #[])
        ((bitRevPerm (d + l)).getD (k.val % 2 ^ (d + l)) 0) := ⟨_, rfl⟩
  rw [← hPV]
  have hPVs : perVals.size = pl.toArray.size * 2 ^ (d + l) := by rw [hPV, Array.size_ofFn]
  have hPVget (c j : Nat) (hj : j < 2 ^ (d + l)) :
      periodicRow (pl.getD c #[]) ((bitRevPerm (d + l)).getD j 0) =
        if c < pl.toArray.size then perVals.getD (c * 2 ^ (d + l) + j) 0 else 0 := by
    split
    · rename_i hc
      have h1 := Nat.mul_le_mul_right (2 ^ (d + l)) (hc : c + 1 ≤ pl.toArray.size)
      rw [Nat.succ_mul] at h1
      have hd : (c * 2 ^ (d + l) + j) / 2 ^ (d + l) = c := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hj,
          Nat.zero_add]
      have hm : (c * 2 ^ (d + l) + j) % 2 ^ (d + l) = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      have hpl : pl.toArray.getD c #[] = pl.getD c #[] := by
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
      rw [hPV, NTTFast.Packed.getD_ofFn_bounded _ _ (by omega), hd, hm, hpl]
    · rename_i hc
      rw [List.size_toArray] at hc
      rw [List.getD_eq_default _ _ (by omega)]
      simp only [periodicRow, Array.size_empty, Array.getD_eq_getD_getElem?,
        Array.getElem?_empty, Option.getD_none]
  rw [parChunks_eq_blocks (2 ^ (d + l) / B) (min (2 ^ (d + l) / B) 16) B _
    (fun j ↦ quotientRow A pis d l (Mat.ofValues s.width (2 ^ (d + l))
      (permuteRows s (bitRevPerm (d + l))))
      (Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))) pl alpha
      ((bitRevPerm (d + l)).getD j 0)) ?_
    (Or.inl (Nat.lt_min.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Nat.two_pow_pos _) hBn) hB0,
      by decide⟩))]
  · show Array.map _ (bitRevPerm (d + l)) = _
    rw [Nat.div_mul_cancel hBn]
    apply Array.ext (by rw [Array.size_map, Array.size_ofFn, size_bitRevPerm])
    intro r h1 h2
    rw [Array.size_ofFn] at h2
    have hP := bitRevPerm_getD_lt (d + l) r h2
    have hPr : (bitRevPerm (d + l))[r]'(by rw [size_bitRevPerm]; exact h2) =
        (bitRevPerm (d + l)).getD r 0 := by
      rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by rw [size_bitRevPerm]; exact h2),
        Option.getD_some]
    rw [Array.getElem_map, Array.getElem_ofFn, hPr, NTTFast.Packed.getD_ofFn_bounded _ _ hP,
      bitRevPerm_getD_getD _ _ h2]
  intro s0 len hlen
  show List.foldl _ (Array.emptyWithCapacity (len * B)) _ = _
  simp only [Nat.add_sub_cancel_left]
  rw [CompStark.Stark.foldl_blocks, Array.emptyWithCapacity_eq, Array.empty_append]
  apply congrArg
  funext r
  have hr : r.val < len * B := r.isLt
  have hlen' : s0 + r.val / B < 2 ^ (d + l) / B := by
    have : r.val / B < len := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm B len]; exact hr)
    rcases hlen with hlen | hlen
    · omega
    · have h0 : len * B = 0 := by rw [hlen, Nat.zero_mul]
      omega
  rw [show s0 * B + r.val = (s0 + r.val / B) * B + r.val % B by
    rw [Nat.add_mul, Nat.add_assoc, Nat.div_add_mod']]
  generalize s0 + r.val / B = blk at hlen' ⊢
  have hi : r.val % B < B := Nat.mod_lt _ hB0
  generalize r.val % B = i at hi ⊢
  have hblkB : blk * B + B ≤ 2 ^ (d + l) := by
    have := Nat.mul_le_mul_right B (hlen' : blk + 1 ≤ 2 ^ (d + l) / B)
    rw [Nat.succ_mul, Nat.div_mul_cancel hBn] at this
    exact this
  have hsizeP : (bitRevPerm (d + l)).size = parts * 2 ^ e := by rw [size_bitRevPerm, hpe]
  let E (j : Nat) : Expr.Env F F := rowEnv (Mat.ofValues s.width (2 ^ (d + l))
    (permuteRows s (bitRevPerm (d + l))))
    (Mat.ofValues sp.width (2 ^ (d + l)) (permuteRows sp (bitRevPerm (d + l)))) pl
    (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) ((bitRevPerm (d + l)).getD j 0)
  have hsel (sel : Array F) (j : Nat) (hj : j < parts * 2 ^ e) :
      sel.getD ((bitRevPerm (d + l)).getD j 0) 0 =
        ((bitRevPerm (d + l)).map fun i ↦ sel.getD i 0).getD j 0 := by
    rw [getD_map_lt _ _ j (by rw [hsizeP]; exact hj) 0 0]
  have hV : ∀ a ∈ weighted A alpha, evalWords
      (encode (colsOf s.values s.width parts (2 ^ e)))
      (encode (colsOf sp.values sp.width parts (2 ^ e))) (encode perVals) s.width sp.width
      pl.toArray.size (2 ^ (d + l)) (2 ^ e) B T.next T.contiguous pis
      (encode ((bitRevPerm (d + l)).map fun i ↦ (qFirst d l : Array F).getD i 0))
      (encode ((bitRevPerm (d + l)).map fun i ↦ (qLast d l : Array F).getD i 0))
      (encode ((bitRevPerm (d + l)).map fun i ↦ (qTrans d l : Array F).getD i 0)) (blk * B) a.1 =
      encode (Array.ofFn (n := B) fun k ↦ a.1.eval (E (blk * B + k.val))) := by
    intro a ha
    have hc' : a.1 ∈ A.constraints := (List.of_mem_zip ha).1
    refine evalWords_eq s.values sp.values perVals s.width sp.width pl.toArray.size (2 ^ (d + l))
      parts (2 ^ e) B T.next T.contiguous
      pis _ _ _ (blk * B) E (Nat.two_pow_pos e) hBR hB0 (Dvd.intro_left blk rfl)
      (by rw [hpe]; exact hblkB) hM hus hMp husp (by rw [hPVs]) hblkB
      (by have := USize.le_size; omega) ?_ ?_ (by rw [Array.size_map, hsizeP, hpe]; exact hblkB)
      (by rw [Array.size_map, hsizeP, hpe]; exact hblkB)
      (by rw [Array.size_map, hsizeP, hpe]; exact hblkB) ?_ ?_ ?_ ?_
      (fun j hj c ↦ hPVget c j (by rw [← hpe]; exact hj)) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun j hj ↦ hsel _ j hj) (fun j hj ↦ hsel _ j hj) (fun j hj ↦ hsel _ j hj)
      a.1 (hc _ hc')
    · intro j hj
      rw [hpe] at hj ⊢
      rw [hnext j hj]
      exact bitRevPerm_getD_lt _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
    · intro n0 h0
      rw [Nat.mul_div_cancel _ hB0] at h0
      exact hcont blk n0 h0
    · intro j hj c hc
      rw [hpe] at hj
      show (permuteRows s (bitRevPerm (d + l))).getD ((bitRevPerm (d + l)).getD j 0 * s.width + c)
        0 = _
      rw [permuteRows_getD s _ _ c (by rw [size_bitRevPerm]; exact bitRevPerm_getD_lt _ _ hj) hc,
        bitRevPerm_getD_getD _ _ hj]
    · intro j hj c hc
      rw [hpe] at hj
      show (permuteRows s (bitRevPerm (d + l))).getD
        ((((bitRevPerm (d + l)).getD j 0 + 2 ^ l) % 2 ^ (d + l)) * s.width + c) 0 = _
      rw [permuteRows_getD s _ _ c (by rw [size_bitRevPerm]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
        hc, hnext j hj]
    · intro j hj c hc
      rw [hpe] at hj
      show (permuteRows sp (bitRevPerm (d + l))).getD
        ((bitRevPerm (d + l)).getD j 0 * sp.width + c) 0 = _
      rw [permuteRows_getD sp _ _ c (by rw [size_bitRevPerm]; exact bitRevPerm_getD_lt _ _ hj)
        hc, bitRevPerm_getD_getD _ _ hj]
    · intro j hj c hc
      rw [hpe] at hj
      show (permuteRows sp (bitRevPerm (d + l))).getD
        ((((bitRevPerm (d + l)).getD j 0 + 2 ^ l) % 2 ^ (d + l)) * sp.width + c) 0 = _
      rw [permuteRows_getD sp _ _ c
        (by rw [size_bitRevPerm]; exact Nat.mod_lt _ (Nat.two_pow_pos _)) hc, hnext j hj]
  have hw4 : ∀ a ∈ weighted A alpha, a.2.length = 4 := fun a ha ↦ by
    obtain ⟨-, h2⟩ := List.of_mem_zip ha
    obtain ⟨k, -, hk⟩ := List.mem_map.mp h2
    rw [← hk]
    rfl
  have hzip : A.constraints.zip ((List.range A.constraints.length).map fun k ↦
      (Ext.coeffs (Ext.pow alpha (A.constraints.length - 1 - k))).map Subtype.val) =
      (weighted A alpha).map fun a ↦ (a.1, a.2.map Subtype.val) := by
    simp only [weighted, List.zip_map_right, List.map_map]
    rfl
  rw [hzip, EVec.zeroWords_ofFn (p := p)]
  have hacc := accWords B (by have := USize.le_size; omega) _
    (fun c k ↦ c.eval (E (blk * B + k))) (weighted A alpha) hV hw4 (fun _ _ ↦ 0)
  beta_reduce at hacc
  rw [hacc]
  have hBs : 4 * B < USize.size := by have := USize.le_size; omega
  rw [(getElem!_lit4 _ _ _ _).1, (getElem!_lit4 _ _ _ _).2.1, (getElem!_lit4 _ _ _ _).2.2.1,
    (getElem!_lit4 _ _ _ _).2.2.2]
  have hrd (j : Nat) := word_encode_ofFn B hBs
    (fun k ↦ rowAcc (weighted A alpha) (fun c ↦ c.eval (E (blk * B + k))) j 0) i hi
  rw [hrd 0, hrd 1, hrd 2, hrd 3]
  unfold quotientRow
  rfl

end CompStark.Stark.Fast
