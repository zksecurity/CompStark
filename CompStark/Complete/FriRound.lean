/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Complete.Fold
public import CompStark.Complete.Merkle
public import CompStark.Fri.Shapes

/-! # A commit round's opening

The prover commits to the groups of `2 ^ la` entries of a vector as rows and answers a query at
`idx` with the group of `idx` minus the entry at `idx`, the siblings. The verifier puts the running
value back between the siblings and recovers the group (`evals_answer`), whose coefficients are
the committed row (`row_leaves`), so the opening verifies (`verifyBatch_answer`).
-/

@[expose] public section
namespace CompStark.Complete
open CompStark.Stark CompStark.Fri

variable {F : Type} [BaseField F]
local notation "hashF" => CompStark.Hash.Poseidon2.hash F
local notation "compF" => CompStark.Hash.Poseidon2.compress F

variable {EF : Type} [Challenge F EF]

/-- The indices below `n` other than `p`. -/
theorem filter_range (n p : Nat) (hp : p < n) :
    (List.range n).filter (· != p) = List.range p ++ List.range' (p + 1) (n - p - 1) := by
  have hr : List.range n = List.range p ++ [p] ++ List.range' (p + 1) (n - p - 1) := by
    have e : n = p + (1 + (n - p - 1)) := by omega
    conv_lhs => rw [e, List.range_eq_range', ← List.range'_append_1, ← List.range'_append_1]
    simp only [Nat.zero_add, List.range'_one, List.range_eq_range', List.append_assoc]
  rw [hr, List.filter_append, List.filter_append, List.filter_singleton, bne_self_eq_false,
    Bool.cond_false, List.append_nil, List.filter_eq_self.mpr, List.filter_eq_self.mpr]
  · intro a ha
    rw [List.mem_range'_1] at ha
    simp only [bne_iff_ne, ne_eq]
    omega
  · intro a ha
    rw [List.mem_range] at ha
    simp only [bne_iff_ne, ne_eq]
    omega

theorem length_filter_range (n p : Nat) (hp : p < n) :
    ((List.range n).filter (· != p)).length = n - 1 := by
  rw [filter_range n p hp, List.length_append, List.length_range, List.length_range']
  omega

theorem getD_filter_range (n p j : Nat) (hp : p < n) (hj : j < n - 1) :
    ((List.range n).filter (· != p)).getD j 0 = if j < p then j else j + 1 := by
  rw [filter_range n p hp, List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by rw [List.length_range]; omega), List.getElem?_range (by
      omega), Option.getD_some]
  · rw [List.getElem?_append_right (by rw [List.length_range]; omega), List.length_range,
      List.getElem?_range' (by omega), Option.getD_some]
    omega

/-- Putting the running value back between the siblings recovers the group. -/
theorem evals_answer (a pos : Nat) (hpos : pos < a) (ev : List EF) (eval : EF)
    (he : eval = ev.getD pos 0) :
    (List.range a).map (fun j ↦
      if j < pos then (((List.range a).filter (· != pos)).map fun j ↦ ev.getD j 0).toArray.getD j 0
      else if j = pos then eval
      else (((List.range a).filter (· != pos)).map fun j ↦ ev.getD j 0).toArray.getD (j - 1) 0) =
      (List.range a).map fun j ↦ ev.getD j 0 := by
  have hs : ∀ i < a - 1, (((List.range a).filter (· != pos)).map fun j ↦ ev.getD j 0).toArray.getD
      i 0 = ev.getD (if i < pos then i else i + 1) 0 := by
    intro i hi
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [length_filter_range a pos hpos]; exact hi),
      Option.map_some, Option.getD_some, ← List.getD_eq_getElem _ 0,
      getD_filter_range a pos i hpos hi]
  refine List.map_congr_left fun j hj ↦ ?_
  have hj := List.mem_range.mp hj
  split
  · rw [hs j (by omega), ite_eq_left (by assumption)]
  · split
    · subst_vars; rfl
    · rw [hs (j - 1) (by omega), ite_eq_right (by omega), Nat.sub_add_cancel (by omega)]

/-- Entry `t` of flattened coordinates is coordinate `t % d` of element `t / d`. -/
theorem getD_flatMap_coeffs_list : ∀ (l : List EF) (t : Nat), t < Challenge.d EF * l.length →
    (l.flatMap Ext.coeffs).getD t 0 =
      (Ext.coeffs (l.getD (t / Challenge.d EF) 0)).getD (t % Challenge.d EF) 0
  | [], t, h => by rw [List.length_nil, Nat.mul_zero] at h; omega
  | x :: l, t, h => by
    have hl : (Ext.coeffs x).length = Challenge.d EF := Challenge.length_coeffs x
    rw [List.flatMap_cons]
    by_cases ht : t < Challenge.d EF
    · rw [List.getD_append _ _ _ _ (by rw [hl]; exact ht), Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht,
        List.getD_cons_zero]
    · rw [List.length_cons, Nat.mul_succ] at h
      have hd : 0 < Challenge.d EF := (Challenge.params EF).d_pos
      have e1 : t / Challenge.d EF = (t - Challenge.d EF) / Challenge.d EF + 1 :=
        Nat.div_eq_sub_div (by omega) (by omega)
      have e2 : t % Challenge.d EF = (t - Challenge.d EF) % Challenge.d EF :=
        Nat.mod_eq_sub_mod (by omega)
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl,
        getD_flatMap_coeffs_list l _ (by omega), e1, e2, List.getD_cons_succ]

theorem getD_flatMap_coeffs (A : Array EF) (t : Nat) (ht : t < Challenge.d EF * A.size) :
    (A.flatMap fun x ↦ (Ext.coeffs x).toArray).getD t 0 =
      (Ext.coeffs (A.getD (t / Challenge.d EF) 0)).getD (t % Challenge.d EF) 0 := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, Array.toList_flatMap,
    ← List.getD_eq_getElem?_getD]
  rw [show (A.toList.flatMap fun x ↦ Ext.coeffs x) = A.toList.flatMap Ext.coeffs from rfl,
    getD_flatMap_coeffs_list _ _ (by rw [Array.length_toList]; exact ht),
        Array.getD_eq_getD_getElem?,
    ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD]

/-- Row `r` of a round's leaves is the coefficients of the group of `r`. -/
theorem rowOf_leaves [Poseidon2Field F] (f : Array EF) (la r : Nat) (hr : (r + 1) * 2 ^ la ≤
    f.size) :
    (rowOf ((specBackend EF).leaves (2 ^ la) f) r).toList =
      ((List.range (2 ^ la)).map fun k ↦ f.getD (r * 2 ^ la + k) 0).flatMap Ext.coeffs := by
  have hd : 0 < Challenge.d EF := (Challenge.params EF).d_pos
  set G := (List.range (2 ^ la)).map fun k ↦ f.getD (r * 2 ^ la + k) 0 with hG
  have hGl : G.length = 2 ^ la := by rw [hG, List.length_map, List.length_range]
  have hlen : (G.flatMap Ext.coeffs).length = Challenge.d EF * 2 ^ la := by
    rw [List.length_flatMap]
    simp only [Ext.coeffs, Challenge.length_coeffs]
    rw [List.map_const', List.sum_replicate, hGl, smul_eq_mul, Nat.mul_comm]
  refine List.ext_getElem (by
    simp only [Array.length_toList, rowOf, Array.size_ofFn, hlen]; rfl) fun j h1 h2 ↦ ?_
  rw [hlen] at h2
  simp only [Array.getElem_toList, rowOf, Array.getElem_ofFn]
  rw [← List.getD_eq_getElem _ 0,
    getD_flatMap_coeffs_list _ _ (by rw [hGl]; exact h2)]
  show (f.flatMap fun x ↦ (Ext.coeffs x).toArray).getD (r * (Challenge.d EF * 2 ^ la) + j) 0 = _
  rw [Nat.succ_mul] at hr
  have hj : j / Challenge.d EF < 2 ^ la := Nat.div_lt_of_lt_mul h2
  rw [getD_flatMap_coeffs f _ (by nlinarith [Nat.mod_add_div j (Challenge.d EF)]),
    show r * (Challenge.d EF * 2 ^ la) + j = Challenge.d EF * (r * 2 ^ la) + j by ring,
    Nat.mul_add_div hd, Nat.mul_add_mod]
  congr 2
  rw [hG, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj),
        List.getElem_map,
        List.getElem_range]

/-- A round's answer at `idx`: `2 ^ la - 1` siblings, which with the running value give back the
group of `idx`, and whose opening verifies. -/
theorem answer_round [Poseidon2Field F] (f : Array EF) (h la idx : Nat) (hs : f.size = 2 ^ h) (hla
    : la ≤ h)
    (hidx : idx < 2 ^ h) :
    let c := Committed.ofMats hashF compF [(specBackend EF).leaves (2 ^ la) f]
    let o := c.openAt (idx >>> la)
    let pos := idx % 2 ^ la
    let ev := unflatten ((o.values.getD 0 #[]).toList)
    let sib := (((List.range (2 ^ la)).filter (· != pos)).map fun j ↦ ev.getD j 0).toArray
    let evals := (List.range (2 ^ la)).map fun j ↦
      if j < pos then sib.getD j 0 else if j = pos then f.getD idx 0 else sib.getD (j - 1) 0
    sib.size = 2 ^ la - 1 ∧
      evals = (List.range (2 ^ la)).map (fun k ↦ f.getD ((idx >>> la) * 2 ^ la + k) 0) ∧
      Merkle.Poseidon2.verifyBatch F c.root [2 ^ (h - la)] (idx >>> la)
        [evals.flatMap Ext.coeffs] o.path.toList = true := by
  intro c o pos ev sib evals
  have hapos : 0 < 2 ^ la := by positivity
  have hpos : pos < 2 ^ la := Nat.mod_lt _ hapos
  have hr : idx >>> la = idx / 2 ^ la := Nat.shiftRight_eq_div_pow idx la
  have hhl : 2 ^ h = 2 ^ (h - la) * 2 ^ la := by rw [← pow_add, Nat.sub_add_cancel hla]
  have hrlt : idx >>> la < 2 ^ (h - la) := by
    rw [hr]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hhl]; exact hidx)
  have hridx : (idx >>> la) * 2 ^ la + pos = idx := by
    rw [hr, Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hrb : (idx >>> la + 1) * 2 ^ la ≤ f.size := by
    rw [hs, hhl]; exact Nat.mul_le_mul_right _ hrlt
  set G := (List.range (2 ^ la)).map fun k ↦ f.getD ((idx >>> la) * 2 ^ la + k) 0 with hG
  have hm : ((specBackend EF).leaves (2 ^ la) f).height = 2 ^ (h - la) := by
    show f.size / 2 ^ la = _
    rw [hs, hhl, Nat.mul_div_cancel _ hapos]
  have hvals : o.values = #[rowOf ((specBackend EF).leaves (2 ^ la) f) (idx >>> la)] :=
    openAt_values _ (h - la) (fun m hm' ↦ by rw [List.mem_singleton.mp hm']; exact hm) _
  have hev : ev = G := by
    show unflatten ((o.values.getD 0 #[]).toList) = G
    rw [hvals]
    show unflatten (rowOf _ _).toList = G
    rw [rowOf_leaves f la _ hrb]
    exact unflatten_flatMap G
  have hevals : evals = G := by
    show (List.range (2 ^ la)).map _ = G
    rw [evals_answer (2 ^ la) pos hpos ev (f.getD idx 0) (by
      rw [hev, hG,
        List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hpos),
        List.getElem_map, List.getElem_range, hridx]), hev]
    exact List.map_congr_left fun j hj ↦ by
      rw [List.getD_eq_getElem _ _ (by rw [hG]; simpa using hj),
        List.getElem_map,
        List.getElem_range]
  refine ⟨?_, hevals, ?_⟩
  · show (List.map _ _).toArray.size = _
    rw [List.size_toArray, List.length_map, length_filter_range _ _ hpos]
  · have hv := verifyBatch_openAt [(specBackend EF).leaves (2 ^ la) f] (h - la) (List.cons_ne_nil
      _ _)
      (fun m hm' ↦ by
        rw [List.mem_singleton.mp hm']
        refine ⟨hm, ?_⟩
        show (f.flatMap fun x ↦ (Ext.coeffs x).toArray).size =
          Challenge.d EF * 2 ^ la * (f.size / 2 ^ la)
        rw [size_flatMap_coeffs, hs, hhl, Nat.mul_div_cancel _ hapos]
        ring) (idx >>> la) hrlt
    replace hv : Merkle.Poseidon2.verifyBatch F c.root [2 ^ (h - la)] (idx >>> la)
        (o.values.toList.map (·.toList)) o.path.toList = true := by
      rw [← hm]; exact hv
    rw [hevals]
    have : o.values.toList.map (·.toList) = [G.flatMap Ext.coeffs] := by
      rw [hvals, ← rowOf_leaves f la _ hrb]; rfl
    rw [← this]
    exact hv

end CompStark.Complete
