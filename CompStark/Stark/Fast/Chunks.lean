/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Stark.Fast.Lde
public import CompStark.Stark.Fast.Vectors
public import CompStark.Stark.Fast.Openings
public import CompStark.Stark.Refines

/-! # The fast quotient chunks are the specification's

`chunksWith` extends every coordinate of every quotient chunk from its column, gathered from the
coordinate's plane in the extension's bit-reversed order: that column is the chunk's column of
`chunkValues`, so its blocks are
`ldeSpec`'s (`blocks_ldeSpec`) and the chunk represents `ldeRef` (`rm_ldeRef`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (LdePlan column getD_map_range flatMap_range_map)
open CompPoly.CPolynomial
open Montgomery.Native32.Words (upto upto_zero upto_full write_upto zeroWords_eq read_encode)
open CompPoly.CPolynomial.NTTFast.Packed.Native (zeroWords read write)
open Montgomery.Native32

variable {p : ℕ} [Mont32Field p] {EF : Type} [FastExt p EF]

local notation "F" => FastField p

/-- A coordinate of the specification's coordinates is the element's. -/
theorem coordOf_eq [Mont32BaseField p] [Mont32.AlgebraId EF] (k : Nat) (x : EF) :
    (coordOf k x : F) = coord k x := by
  unfold coordOf coord
  rw [Ext.coeffs, Mont32.coeffs_eq]
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact h), List.getElem_ofFn]
  · rename_i h
    have hd : FastExt.d p EF = (FastExt.params (p := p) EF).d := rfl
    rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]

/-- Words `base + perm[r]` of a packed array. -/
theorem permuted_encode (A : Array F) (base : Nat) (perm : Array Nat) (count : Nat)
    (hA : ∀ r < count, base + perm.getD r 0 < A.size) (hs : 4 * A.size < USize.size)
    (hc : 4 * count < USize.size) :
    permuted (encode A) base perm count =
      encode (Array.ofFn (n := count) fun r ↦ A.getD (base + perm.getD r.val 0) 0) := by
  unfold permuted
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  let f (r : Nat) : F := A.getD (base + perm.getD r 0) 0
  have ho : 4 * (Array.replicate count (0 : F)).size < USize.size := by
    rw [Array.size_replicate]; exact hc
  have key : ∀ K ≤ count, (List.range K).foldl (fun b r ↦ write b r
      (read (encode A) (base + perm.getD r 0))) (zeroWords count) =
      encode (upto (Array.replicate count 0) f K) := by
    intro K hK
    induction K with
    | zero => rw [List.range_zero, List.foldl_nil, zeroWords_eq (p := p), upto_zero]
    | succ K ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        read_encode _ _ hs (hA K (by omega)),
        write_upto _ f _ (by rw [Array.size_replicate]; omega) ho]
  rw [key count le_rfl, upto_full _ _ _ (Array.size_replicate ..)]

/-- Coordinate `k` of chunk `c`, gathered from its plane in the extension's bit-reversed order, is
the chunk's column `k`. -/
theorem permuted_plane [Mont32BaseField p] [Mont32.AlgebraId EF] {v : ExtPlanes p EF}
    {a : Array EF} (hv : QRel v a) (logN l c k : Nat)
    (hc : c < 2 ^ l) (hk : k < FastExt.d p EF) (ha : a.size = 2 ^ (logN + l))
    (hs : 4 * a.size < USize.size) :
    permuted (v.c.toArray.getD k .empty) (2 ^ logN * NTT.Transform.bitRevNat l c)
        (bitRevPerm logN) (2 ^ logN) =
      encode (column (chunkValues a (2 ^ l) c (2 ^ logN)) (FastExt.d p EF) (2 ^ logN) k).toArray
    := by
  have hpl : v.c.toArray.getD k .empty =
      encode ((bitRevValues a).map (FastExt.coord · ⟨k, hk⟩)) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk),
      Option.getD_some, Vector.getElem_toArray]
    exact hv.2 ⟨k, hk⟩
  have hbl := NTT.Transform.bitRevNat_lt l c
  have hidx (r : Nat) (hr : r < 2 ^ logN) :
      2 ^ logN * NTT.Transform.bitRevNat l c + (bitRevPerm logN).getD r 0 < a.size := by
    rw [ha, bitRevPerm_getD _ _ hr, Nat.pow_add]
    have := NTT.Transform.bitRevNat_lt logN r
    have := Nat.mul_le_mul_left (2 ^ logN) (show NTT.Transform.bitRevNat l c + 1 ≤ 2 ^ l by omega)
    rw [Nat.mul_succ] at this
    omega
  have hsz : (bitRevValues a).size = a.size := by rw [bitRevValues, Array.size_ofFn]
  rw [hpl, permuted_encode _ _ _ _ (fun r hr ↦ by rw [Array.size_map, hsz]; exact hidx r hr)
    (by rw [Array.size_map, hsz]; exact hs) (by
      have : 2 ^ logN ≤ a.size := by
        rw [ha]; exact Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
      omega)]
  refine congrArg encode (Array.ext (by simp only [Array.size_ofFn, Vector.size_toArray])
    fun r h1 _ ↦ ?_)
  rw [Array.size_ofFn] at h1
  have hd : 0 < FastExt.d p EF := (FastExt.params (p := p) EF).d_pos
  have hlt : r * FastExt.d p EF + k < 2 ^ logN * Challenge.d EF := by
    rw [Mont32.d_eq]
    have := Nat.mul_le_mul_right (FastExt.d p EF) (show r + 1 ≤ 2 ^ logN by omega)
    rw [Nat.succ_mul] at this
    omega
  have hj := hidx r h1
  -- The bit-reversed index of chunk `c`'s row `r` is the quotient domain's row `r 2 ^ l + c`.
  have hrev : NTT.Transform.bitRevNat (Nat.log2 a.size)
      (2 ^ logN * NTT.Transform.bitRevNat l c + (bitRevPerm logN).getD r 0) = r * 2 ^ l + c := by
    rw [ha, Nat.log2_two_pow, bitRevPerm_getD _ _ h1, Nat.add_comm logN l,
      CompPoly.CPolynomial.NTTFast.Packed.bitRevNat_concat l logN _ _
        (NTT.Transform.bitRevNat_lt logN r),
      NTT.Transform.bitRevNat_involutive _ _ hc, NTT.Transform.bitRevNat_involutive _ _ h1,
      Nat.mul_comm, Nat.add_comm]
  have hmap : ((bitRevValues a).map (FastExt.coord · ⟨k, hk⟩)).getD
      (2 ^ logN * NTT.Transform.bitRevNat l c + (bitRevPerm logN).getD r 0) 0 =
      FastExt.coord (a.getD (r * 2 ^ l + c) 0) ⟨k, hk⟩ := by
    rw [getD_lt _ _ (by rw [Array.size_map, hsz]; exact hj), Array.getElem_map]
    simp only [bitRevValues, Array.getElem_ofFn]
    rw [hrev]
  rw [Array.getElem_ofFn, Array.getElem_eq_getD 0, getD_column _ _ _ _ _ h1, hmap,
    chunkValues_eq, CompPoly.CPolynomial.NTTFast.Packed.getD_ofFn_bounded _ _ hlt]
  have e1 : (r * FastExt.d p EF + k) / FastExt.d p EF = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hk, Nat.zero_add]
  have e2 : (r * FastExt.d p EF + k) % FastExt.d p EF = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  dsimp only
  rw [Mont32.d_eq, e1, e2, coordOf_eq]
  exact (coord_fin _ ⟨k, hk⟩).symm

/-- **The fast quotient chunks are the specification's**, with plans `plan?` built, for quotient
values on a quotient domain within the two-adic subgroups whose chunks' extensions are
addressable. -/
theorem chunksWith_rel [Mont32BaseField p] [Mont32.AlgebraId EF]
    (plans : List (Nat × Nat × F × LdePlan p))
    (hplans : ∀ e ∈ plans, plan? e.1 e.2.1 e.2.2.1 = some e.2.2.2) (bits logN l : Nat)
    {v : ExtPlanes p EF} {a : Array EF} (hv : QRel v a) (ha : a.size = 2 ^ (logN + l))
    (hb : logN + bits ≤ twoAdicity F) (hs : 4 * a.size < USize.size) :
    List.Forall₂ RM (chunksWith plans bits logN l v) (chunksRef bits logN l a) := by
  unfold chunksWith chunksRef
  rw [List.map_map]
  refine forall₂_map (R := fun c c' ↦ c = c' ∧ c < 2 ^ l) (fun c c' hc ↦ ?_)
    (List.forall₂_same.2 fun x hx ↦ ⟨rfl, List.mem_range.mp hx⟩)
  obtain ⟨rfl, hc⟩ := hc
  obtain ⟨P, hP⟩ := planFor_isSome plans logN bits
    (gen * (gen * powF (twoAdicGen (logN + l)) c)⁻¹) hb
  have hP' := planFor_some hplans hP
  obtain ⟨-, hlog, hbits, -, -⟩ := plan?_some hP'
  have hlogH : P.logH = logN := by
    change P.domain.logN - P.bits = logN
    omega
  simp only [Function.comp_apply, hP, Option.map_some]
  refine rm_ldeRef hP' _ _ _ ?_
  rw [← blocks_ldeSpec]
  unfold columnTasks
  simp only [Array.map_map, Function.comp_def, CompPoly.Tasks.get_spawn]
  rw [← hbits, flatMap_range_congr _ _ (fun t ↦ (Array.range (FastExt.d p EF)).map fun k ↦
    encode (colBlock P (FastExt.d p EF) (chunkValues a (2 ^ l) c (2 ^ logN)) t k)) fun t ht ↦ ?_,
    flatMap_range_map]
  apply Array.ext (by simp only [Array.size_map])
  intro k hk _
  simp only [Array.size_map, Array.size_range] at hk
  simp only [Array.getElem_map, Array.getElem_range]
  rw [getD_map_range _ _ _ ht, permuted_plane hv logN l c k hc hk ha hs, ← hlogH,
    cosetBlock_column]

end CompStark.Stark.Fast
