/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Prover

/-! # The quotient values row by row

`quotientValues` evaluates the constraints in blocks of rows, one array operation per node. Row
`r` of its result is the constraints evaluated at row `r` (`rowEnv`), folded by the powers of
`α` coordinate by coordinate, times the inverse vanishing polynomial (`quotientValues_getD`).
-/

@[expose] public section
namespace CompStark.Stark

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- Row `r` of the quotient domain: the trace's and the preprocessed trace's row `r` and the row
`period` on, cyclically, and the periodic columns' row `r`. -/
def rowEnv (tq pq : Mat F) (per : List (Array F)) (n period : Nat) (pis : List F)
    (first last trans : Array F) (r : Nat) : Expr.Env F F where
  cur c := tq.values.getD (r * tq.width + c) 0
  next c := tq.values.getD (((r + period) % n) * tq.width + c) 0
  prepCur c := pq.values.getD (r * pq.width + c) 0
  prepNext c := pq.values.getD (((r + period) % n) * pq.width + c) 0
  periodic j := periodicRow (per.getD j #[]) r
  pub j := pis.getD j 0
  const c := c
  isFirstRow := first.getD r 0
  isLastRow := last.getD r 0
  isTransition := trans.getD r 0

theorem getD_extract (a : Array F) (r0 B i : Nat) (hi : i < B) :
    (a.extract r0 (r0 + B)).getD i 0 = a.getD (r0 + i) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rfl
  · rename_i h
    rw [Array.getElem?_eq_none (by omega)]

theorem size_evalBlock (tq pq : Mat F) (per : List (Array F)) (n period : Nat) (pis : List F)
    (first last trans : Array F)
    (r0 B : Nat) (hf : r0 + B ≤ first.size) (hl : r0 + B ≤ last.size)
    (ht : r0 + B ≤ trans.size) :
    ∀ e, (evalBlock tq pq per n period pis first last trans r0 B e).size = B
  | .cur _ | .next _ | .prepCur _ | .prepNext _ | .periodic _ => Array.size_ofFn
  | .pub _ | .const _ => Array.size_replicate
  | .isFirstRow => by simp only [evalBlock, Array.size_extract]; omega
  | .isLastRow => by simp only [evalBlock, Array.size_extract]; omega
  | .isTransition => by simp only [evalBlock, Array.size_extract]; omega
  | .add a b | .sub a b | .mul a b => by
    simp only [evalBlock, Array.size_zipWith,
      size_evalBlock tq pq per n period pis first last trans r0 B hf hl ht a,
      size_evalBlock tq pq per n period pis first last trans r0 B hf hl ht b, Nat.min_self]

/-- Entry `i` of a block is the expression at row `r0 + i`. -/
theorem evalBlock_getD (tq pq : Mat F) (per : List (Array F)) (n period : Nat) (pis : List F)
    (first last trans : Array F)
    (r0 B : Nat) (hf : r0 + B ≤ first.size) (hl : r0 + B ≤ last.size)
    (ht : r0 + B ≤ trans.size) (i : Nat) (hi : i < B) :
    ∀ e, (evalBlock tq pq per n period pis first last trans r0 B e).getD i 0 =
      e.eval (rowEnv tq pq per n period pis first last trans (r0 + i))
  | .cur c => by
    simp only [evalBlock, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, dite_true,
      Option.getD_some, Expr.eval, rowEnv]
  | .next c | .prepCur c | .prepNext c | .periodic c => by
    simp only [evalBlock, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, dite_true,
      Option.getD_some, Expr.eval, rowEnv]
  | .pub j => by
    simp only [evalBlock, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true,
      Option.getD_some, Expr.eval, rowEnv]
  | .const c => by
    simp only [evalBlock, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true,
      Option.getD_some, Expr.eval, rowEnv]
  | .isFirstRow => by rw [evalBlock, getD_extract _ _ _ _ hi]; rfl
  | .isLastRow => by rw [evalBlock, getD_extract _ _ _ _ hi]; rfl
  | .isTransition => by rw [evalBlock, getD_extract _ _ _ _ hi]; rfl
  | .add a b | .sub a b | .mul a b => by
    have ha := size_evalBlock tq pq per n period pis first last trans r0 B hf hl ht a
    have hb := size_evalBlock tq pq per n period pis first last trans r0 B hf hl ht b
    simp only [evalBlock, Expr.eval, ← evalBlock_getD tq pq per n period pis first last trans r0 B
      hf hl ht i hi a,
      ← evalBlock_getD tq pq per n period pis first last trans r0 B hf hl ht i hi b,
      Array.getD_eq_getD_getElem?, Array.getElem?_zipWith]
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
    rfl

theorem foldl_push_range' {α : Type} (f : Nat → α) (s : Nat) : ∀ (k : Nat) (out : Array α),
    (List.range' s k).foldl (fun o i ↦ o.push (f i)) out =
      out ++ Array.ofFn (n := k) fun i ↦ f (s + i.val)
  | 0, out => by simp only [List.range'_zero, List.foldl_nil, Array.ofFn_zero, Array.append_empty]
  | k + 1, out => by
    rw [List.range'_succ, List.foldl_cons, foldl_push_range' f (s + 1) k]
    apply Array.toList_inj.mp
    simp only [Array.toList_append, Array.toList_push, Array.toList_ofFn, List.ofFn_succ,
      Fin.val_zero, Nat.add_zero, Fin.val_succ, List.append_assoc, List.singleton_append]
    congr 2
    refine congrArg List.ofFn (funext fun i ↦ ?_)
    rw [Nat.add_assoc, Nat.add_comm 1]

theorem foldl_blocks {α : Type} (g : Nat → Nat → α) (B : Nat) : ∀ (m s : Nat) (out : Array α),
    (List.range' s m).foldl (fun o blk ↦ (List.range' 0 B).foldl (fun o i ↦ o.push (g blk i)) o)
      out = out ++ Array.ofFn (n := m * B) fun r ↦ g (s + r.val / B) (r.val % B)
  | 0, s, out => by
    rw [List.range'_zero, List.foldl_nil, Array.eq_empty_of_size_eq_zero (xs := Array.ofFn _)
      (by rw [Array.size_ofFn, Nat.zero_mul]), Array.append_empty]
  | m + 1, s, out => by
    rw [List.range'_succ, List.foldl_cons, foldl_push_range', foldl_blocks g B m (s + 1),
      Array.append_assoc]
    congr 1
    apply Array.toList_inj.mp
    simp only [Array.toList_append, Array.toList_ofFn]
    rw [Nat.succ_mul, Nat.add_comm (m * B) B, List.ofFn_add]
    congr 1
    · refine congrArg List.ofFn (funext fun i ↦ ?_)
      simp only [Fin.val_castLE, Nat.zero_add, Nat.div_eq_of_lt i.isLt, Nat.add_zero,
        Nat.mod_eq_of_lt i.isLt]
    · refine congrArg List.ofFn (funext fun i ↦ ?_)
      simp only [Fin.val_natAdd]
      have hB : 0 < B := Nat.pos_of_ne_zero fun h ↦ by subst h; exact absurd i.isLt (by omega)
      rw [Nat.add_comm B, Nat.add_div_right _ hB, Nat.add_mod_right, Nat.add_assoc, Nat.add_comm 1]

theorem getD_zipWith (f : F → F → F) (a b : Array F) (i : Nat) (ha : i < a.size)
    (hb : i < b.size) : (Array.zipWith f a b).getD i 0 = f (a.getD i 0) (b.getD i 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_zipWith, Array.getElem?_eq_getElem ha,
    Array.getElem?_eq_getElem hb, Option.getD_some]

/-- Coordinate `j` of the constraints `cw` with their weights at one row, `ev c` the value of
constraint `c`, accumulated onto `x`. -/
def rowAcc (cw : List (Expr F × List F)) (ev : Expr F → F) (j : Nat) (x : F) : F :=
  cw.foldl (fun x a ↦ x + ev a.1 * a.2.getD j 0) x

/-- The weighted constraints accumulated block-wise, `D` coordinate arrays of `B` entries: entry
`i` of coordinate `j` is `rowAcc` at that row. -/
theorem accBlocks (D B : Nat) (ev : Expr F → Array F) (hev : ∀ c, (ev c).size = B) :
    ∀ (cw : List (Expr F × List F)), (∀ a ∈ cw, a.2.length = D) → ∀ (acc : Array (Array F)),
      acc.size = D → (∀ j < D, (acc.getD j #[]).size = B) →
      let res := cw.foldl (fun b a ↦ (b.zip a.2.toArray).map fun x ↦
        Array.zipWith (fun u v ↦ u + v * x.2) x.1 (ev a.1)) acc
      res.size = D ∧ ∀ j < D, (res.getD j #[]).size = B ∧ ∀ i < B,
        (res.getD j #[]).getD i 0 =
          rowAcc cw (fun c ↦ (ev c).getD i 0) j ((acc.getD j #[]).getD i 0)
  | [], _, acc, hs, hj => by
    refine ⟨hs, fun j hj' ↦ ⟨hj j hj', fun i _ ↦ rfl⟩⟩
  | a :: cw, hw, acc, hs, hj => by
    have ha : a.2.toArray.size = D := by
      rw [List.size_toArray]; exact hw a List.mem_cons_self
    have hs' : ((acc.zip a.2.toArray).map fun x ↦
        Array.zipWith (fun u v ↦ u + v * x.2) x.1 (ev a.1)).size = D := by
      rw [Array.size_map, Array.size_zip, hs, ha, Nat.min_self]
    have hget (j : Nat) (hj4 : j < D) : (((acc.zip a.2.toArray).map fun x ↦
        Array.zipWith (fun u v ↦ u + v * x.2) x.1 (ev a.1)).getD j #[]) =
        Array.zipWith (fun u v ↦ u + v * a.2.getD j 0) (acc.getD j #[]) (ev a.1) := by
      have hz : j < (acc.zip a.2.toArray).size := by
        rw [Array.size_zip, hs, ha, Nat.min_self]; exact hj4
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
      rw [Array.getElem?_eq_getElem hz, Option.map_some, Option.getD_some, Array.getElem_zip,
        Array.getElem?_eq_getElem (by omega), Option.getD_some, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [← List.size_toArray, ha]; omega), Option.getD_some]
      rfl
    obtain ⟨h1, h2⟩ := accBlocks D B ev hev cw (fun b hb ↦ hw b (List.mem_cons_of_mem a hb)) _ hs'
      (fun j hj4 ↦ by rw [hget j hj4, Array.size_zipWith, hj j hj4, hev, Nat.min_self])
    refine ⟨h1, fun j hj4 ↦ ⟨(h2 j hj4).1, fun i hi ↦ ?_⟩⟩
    rw [List.foldl_cons, (h2 j hj4).2 i hi, hget j hj4]
    simp only [rowAcc, List.foldl_cons]
    congr 1
    exact getD_zipWith _ _ _ i (by rw [hj j hj4]; exact hi) (by rw [hev]; exact hi)

/-- The specification's tables: the quotient domain's points, the vanishing polynomial on its
period, and the selectors, in natural order. -/
abbrev qPoints (d l : Nat) : Array F := cosetPoints (gen : F) (d + l)
abbrev qZh (d l : Nat) : Array F :=
  Array.ofFn (n := 2 ^ l) fun k ↦ powF ((qPoints d l).getD k 0) (2 ^ d) - 1
abbrev qFirst (d l : Nat) : Array F :=
  Array.ofFn (n := 2 ^ (d + l)) fun i ↦ (qZh d l).getD (i.val % 2 ^ l) 0 *
    (batchInv ((qPoints d l).map (· - 1))).getD i 0
abbrev qLast (d l : Nat) : Array F :=
  Array.ofFn (n := 2 ^ (d + l)) fun i ↦ (qZh d l).getD (i.val % 2 ^ l) 0 *
    (batchInv ((qPoints d l).map (· - (twoAdicGen d)⁻¹))).getD i 0
abbrev qTrans (d l : Nat) : Array F := (qPoints d l).map (· - (twoAdicGen d)⁻¹)

/-- The constraints of `A` with the coordinates of their weights `α ^ (K - 1 - k)`. -/
abbrev weighted (A : Air F) (alpha : EF) : List (Expr F × List F) :=
  A.constraints.zip ((List.range A.constraints.length).map fun k ↦
    Ext.coeffs (Ext.pow alpha (A.constraints.length - 1 - k)))

/-- Row `r` of the quotient: the weighted constraints at row `r`, coordinate by coordinate, over
the vanishing polynomial. -/
def quotientRow (A : Air F) (pis : List F) (d l : Nat) (tq pq : Mat F) (per : List (Array F))
    (alpha : EF) (r : Nat) :
    EF :=
  let env := rowEnv tq pq per (2 ^ (d + l)) (2 ^ l) pis (qFirst d l) (qLast d l) (qTrans d l) r
  let ev (c : Expr F) := c.eval env
  Challenge.smul ((batchInv (qZh d l)).getD (r % 2 ^ l) 0) (Challenge.ofCoeffs
    ((List.range (Challenge.d EF)).map fun j ↦ rowAcc (weighted A alpha) ev j 0))

theorem size_cosetPoints (shift : F) (logN : Nat) : (cosetPoints shift logN).size = 2 ^ logN := by
  simp only [cosetPoints, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  suffices h : ∀ (l : List Nat) (init : Array F × F),
      (l.foldl (fun b _ ↦ (b.1.push b.2, b.2 * twoAdicGen logN)) init).1.size =
        init.1.size + l.length by
    change Array.size (Prod.fst (List.foldl (α := Array F × F) (β := Nat) _ _ _)) = _
    rw [h, List.length_range', Array.emptyWithCapacity_eq, Array.size_empty, Nat.zero_add]
  intro l
  induction l with
  | nil => intro init; rfl
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih, Array.size_push, List.length_cons]
    omega

/-- Row `blk · B + i` of the block-wise evaluation. -/
theorem blockRow (tq pq : Mat F) (per : List (Array F)) (n period : Nat) (pis : List F)
    (first last trans invZh : Array F)
    (D : Nat) (cw : List (Expr F × List F)) (hw : ∀ a ∈ cw, a.2.length = D) (B r : Nat)
    (hB : 0 < B) (hf : (0 + r / B) * B + B ≤ first.size) (hl : (0 + r / B) * B + B ≤ last.size)
    (ht : (0 + r / B) * B + B ≤ trans.size) :
    let acc := cw.foldl (fun b a ↦ (b.zip a.2.toArray).map fun x ↦
      Array.zipWith (fun u v ↦ u + v * x.2) x.1
        (evalBlock tq pq per n period pis first last trans ((0 + r / B) * B) B a.1))
      (Array.replicate D (Array.replicate B 0))
    let ev (c : Expr F) := c.eval (rowEnv tq pq per n period pis first last trans r)
    Challenge.smul (invZh.getD (((0 + r / B) * B + r % B) % period) 0)
      (Challenge.ofCoeffs ((List.range D).map fun j ↦ acc[j]!.getD (r % B) 0) : EF) =
    Challenge.smul (invZh.getD (r % period) 0)
      (Challenge.ofCoeffs ((List.range D).map fun j ↦ rowAcc cw ev j 0)) := by
  intro acc ev
  have hr : (0 + r / B) * B + r % B = r := by rw [Nat.zero_add, Nat.div_add_mod']
  obtain ⟨-, h2⟩ := accBlocks D B
    (fun c ↦ evalBlock tq pq per n period pis first last trans ((0 + r / B) * B) B c)
    (size_evalBlock tq pq per n period pis first last trans _ B hf hl ht) cw hw
    (Array.replicate D (Array.replicate B 0)) Array.size_replicate
    (fun j hj ↦ by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hj, ite_true,
        Option.getD_some, Array.size_replicate])
  have hi : r % B < B := Nat.mod_lt _ hB
  have hrow (j : Nat) (hj : j < D) : acc[j]!.getD (r % B) 0 = rowAcc cw ev j 0 := by
    rw [Array.getElem!_eq_getD, show (default : Array F) = #[] from rfl, (h2 j hj).2 _ hi]
    have h0 : ((Array.replicate D (Array.replicate B (0 : F))).getD j #[]).getD (r % B) 0 = 0 := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hj, hi, ite_true,
        Option.getD_some]
    rw [h0]
    refine congrArg (fun f ↦ rowAcc cw f j 0) (funext fun c ↦ ?_)
    rw [evalBlock_getD tq pq per n period pis first last trans _ B hf hl ht _ hi, hr]
  rw [hr, List.map_congr_left fun j hj ↦ hrow j (List.mem_range.mp hj)]

theorem quotientValues_eq (A : Air F) (pis : List F) (d l : Nat) (tq pq : Mat F)
    (per : List (Array F)) (alpha : EF) :
    quotientValues A pis d l tq pq per alpha =
      Array.ofFn (n := 2 ^ (d + l)) fun r ↦ quotientRow A pis d l tq pq per alpha r.val := by
  simp only [quotientValues, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [foldl_blocks]
  have hB : 0 < min (2 ^ (d + l)) 256 := Nat.lt_min.mpr ⟨Nat.two_pow_pos _, by decide⟩
  have hdvd : min (2 ^ (d + l)) 256 ∣ 2 ^ (d + l) := by
    by_cases h : 2 ^ (d + l) ≤ 256
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right (by omega), show (256 : Nat) = 2 ^ 8 from rfl]
      refine Nat.pow_dvd_pow 2 ?_
      by_contra h'
      exact h (le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (le_refl (2 ^ 8)))
  have hn : 2 ^ (d + l) / min (2 ^ (d + l)) 256 * min (2 ^ (d + l)) 256 = 2 ^ (d + l) :=
    Nat.div_mul_cancel hdvd
  have hw : ∀ a ∈ weighted A alpha, a.2.length = Challenge.d EF := fun a ha ↦ by
    obtain ⟨-, h2⟩ := List.of_mem_zip ha
    obtain ⟨k, -, hk⟩ := List.mem_map.mp h2
    rw [← hk]
    exact Challenge.length_coeffs _
  show (Array.emptyWithCapacity _ ++ _ : Array EF) = _
  rw [Array.emptyWithCapacity_eq, Array.empty_append]
  apply Array.ext
  · rw [Array.size_ofFn, Array.size_ofFn, hn]
  · intro r h1 h2
    rw [Array.size_ofFn] at h2
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    have hle : (0 + r / min (2 ^ (d + l)) 256) * min (2 ^ (d + l)) 256 + min (2 ^ (d + l)) 256 ≤
        2 ^ (d + l) := by
      rw [Nat.zero_add]
      have : r / min (2 ^ (d + l)) 256 < 2 ^ (d + l) / min (2 ^ (d + l)) 256 :=
        (Nat.div_lt_div_of_lt_of_dvd hdvd h2)
      calc r / min (2 ^ (d + l)) 256 * min (2 ^ (d + l)) 256 + min (2 ^ (d + l)) 256
          = (r / min (2 ^ (d + l)) 256 + 1) * min (2 ^ (d + l)) 256 := by ring
        _ ≤ 2 ^ (d + l) / min (2 ^ (d + l)) 256 * min (2 ^ (d + l)) 256 :=
          Nat.mul_le_mul_right _ this
        _ = 2 ^ (d + l) := hn
    unfold quotientRow
    exact blockRow tq pq per _ _ pis (qFirst d l) (qLast d l) (qTrans d l) (batchInv (qZh d l))
      _ (weighted A alpha) hw _ r hB
      (by rw [qFirst, Array.size_ofFn]; exact hle) (by rw [qLast, Array.size_ofFn]; exact hle)
      (by rw [qTrans, Array.size_map, qPoints, size_cosetPoints]; exact hle)

end CompStark.Stark
