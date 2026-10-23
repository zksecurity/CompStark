/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Plonky3.Primitives
public import CompStark.Stark.Fast.Commit

/-! # The fast verifier

Plonky3's verifier `verify` over a 32-bit Montgomery field with packed Poseidon2 kernels, computed
faster (`verifyFast`, equal to `verify` by `verifyFast_eq`):

* Every Merkle multi-opening hashes its leaves eight at a time in the lanes of packed width-24
  groups (`hashRows`, `Merkle.Packed.hashRange`).
* The batched quotient of a query, `∑ αⁱ (pᵢ(z) - pᵢ(x)) / (z - x)` over a matrix's columns, is
  `(∑ αⁱ pᵢ(z) - ∑ αⁱ pᵢ(x)) / (z - x)`: the opened values' sum `∑ αⁱ pᵢ(z)` is the same for every
  query and is computed once (`annotate`), and the row's `∑ αⁱ pᵢ(x)` takes one multiplication by
  a base element per column, by the powers of `α` computed once (`dotBase`).
-/

@[expose] public section
namespace CompStark.Stark.Fast
open CompStark.Fri
open CompPoly.PackedRepr (encode)
open CompStark.Poseidon2 Montgomery.Native32

/-- Entry `r · w + j` of rows of width `w` laid end to end is entry `j` of row `r`. -/
theorem getD_flatten_uniform {α : Type} (d : α) (xss : List (List α)) (w : Nat) (h : ∀ xs ∈ xss, xs.length = w)
    (r j : Nat) (hr : r < xss.length) (hj : j < w) :
    xss.flatten.toArray.getD (r * w + j) d = (xss.getD r []).getD j d := by
  induction xss generalizing r with
  | nil => simp only [List.length_nil] at hr; omega
  | cons xs xss ih =>
    have hxs : xs.length = w := h xs List.mem_cons_self
    rw [List.flatten_cons]
    cases r with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero]
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_append_left
        (by omega), ← List.getD_eq_getElem?_getD]
    | succ r =>
      have hr' : r < xss.length := by simp only [List.length_cons] at hr; omega
      have := ih (fun ys hy ↦ h ys (List.mem_cons_of_mem _ hy)) r hr'
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray] at this ⊢
      rw [List.getElem?_append_right (by rw [hxs, Nat.succ_mul]; omega), hxs,
        show (r + 1) * w + j - w = r * w + j by rw [Nat.succ_mul]; omega, this,
        List.getD_cons_succ]

section Monad

variable {F : Type} {m : Type → Type} [Monad m] (H : Primitives F m)

theorem ensure_bind_congr [LawfulMonad m] {β : Type} (c : Bool) (msg : String) (k1 k2 : Unit → M H β)
    (h : c = true → k1 () = k2 ()) : (ensure c msg >>= k1) = (ensure c msg >>= k2) := by
  cases c
  · funext s
    simp only [bind, StateT.bind, ExceptT.bind, ExceptT.mk, ensure, Bool.false_eq_true,
      ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Function.comp_apply, StateT.lift, pure_bind,
      ExceptT.bindCont]
  · simp only [ensure, ↓reduceIte, pure_bind, h rfl]

theorem forIn_congr_mem {α β : Type} (l : List α) (b : β) (f g : α → β → M H (ForInStep β))
    (h : ∀ a ∈ l, ∀ s, f a s = g a s) : forIn l b f = forIn l b g := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons]
    rw [h a List.mem_cons_self]
    congr 1
    funext r
    cases r with
    | done => rfl
    | yield r => exact ih r fun a ha ↦ h a (List.mem_cons_of_mem _ ha)

end Monad

/-! ### Batched quotients with shared sums -/

section Reduce
open Challenge

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- `a, a α, …, a α ^ (n - 1)`. -/
def powersFrom (alpha : EF) : Nat → EF → List EF
  | 0, _ => []
  | n + 1, a => a :: powersFrom alpha n (a * alpha)

/-- `(∑ αⁱ yᵢ, α ^ n)` of `n` values `ys`. -/
def powSum (alpha : EF) (ys : List EF) : EF × EF :=
  ys.foldl (fun (s, a) y ↦ (s + a * y, a * alpha)) (0, 1)

/-- `∑ xᵢ wᵢ` of base elements and extension weights, by multiplications by base elements. -/
def dotBase (xs : List F) (ws : List EF) : EF :=
  (xs.zip ws).foldl (fun d (x, w) ↦ d + smul x w) 0

/-- A matrix of a round for `reduceQueryWith`: its domain, the powers of `α` up to its widest
opened row, and its opening points with `powSum` of their values. -/
abbrev Annotated (F EF : Type) := Domain F × Array EF × List ((EF × List EF) × EF × EF)

/-- The rounds' matrices with the sums `reduceQueryWith` shares between queries. -/
def annotate (alpha : EF) (rounds : List (Round F EF)) : List (List (Annotated F EF)) :=
  rounds.map fun (_, mats) ↦ mats.map fun (d, pts) ↦
    (d, (powersFrom alpha (pts.foldl (fun l (_, ys) ↦ max l ys.length) 0) 1).toArray,
      pts.map fun pt ↦ (pt, powSum alpha pt.2))

theorem toSpec_getD_powersFrom (alpha : EF) (n : Nat) (a : EF) (i : Nat) (hi : i < n) :
    toSpec ((powersFrom alpha n a).getD i 0) = toSpec a * toSpec alpha ^ i := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rw [powersFrom, List.getD_cons_zero, pow_zero, mul_one]
    | succ i =>
      rw [powersFrom, List.getD_cons_succ, ih _ _ (by omega), toSpec_mul, pow_succ]
      ring

theorem length_powersFrom (alpha : EF) (n : Nat) (a : EF) : (powersFrom alpha n a).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [powersFrom, List.length_cons, ih]

theorem le_foldl_max {α : Type} (f : α → Nat) (l : List α) (n : Nat) :
    n ≤ l.foldl (fun k a ↦ max k (f a)) n ∧ ∀ a ∈ l, f a ≤ l.foldl (fun k a ↦ max k (f a)) n := by
  induction l generalizing n with
  | nil => exact ⟨le_rfl, fun a ha ↦ absurd ha List.not_mem_nil⟩
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := ih (max n (f b))
    refine ⟨le_trans (le_max_left _ _) h1, fun a ha ↦ ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_trans (le_max_right _ _) h1
    · exact h2 a ha

theorem sum_pow_succ {K : Type} [CommRing K] (c : K) (f : Nat → K) (n : Nat) :
    ∑ i ∈ Finset.range n, c ^ (i + 1) * f i = c * ∑ i ∈ Finset.range n, c ^ i * f i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [pow_succ']; ring

theorem powSum_foldl (alpha : EF) (ys : List EF) (s a : EF) :
    toSpec (ys.foldl (fun (s, a) y ↦ (s + a * y, a * alpha)) (s, a)).1 =
      toSpec s + toSpec a * ∑ i ∈ Finset.range ys.length,
        toSpec alpha ^ i * toSpec (ys.getD i 0) ∧
    toSpec (ys.foldl (fun (s, a) y ↦ (s + a * y, a * alpha)) (s, a)).2 =
      toSpec a * toSpec alpha ^ ys.length := by
  induction ys generalizing s a with
  | nil => simp only [List.foldl_nil, List.length_nil, Finset.range_zero, Finset.sum_empty,
      mul_zero, add_zero, pow_zero, mul_one, and_self]
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih (s + a * y) (a * alpha)
    rw [List.foldl_cons]
    refine ⟨?_, ?_⟩
    · rw [h1, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [sum_pow_succ]
      simp only [toSpec_add, toSpec_mul]
      ring
    · rw [h2, toSpec_mul, List.length_cons, pow_succ]
      ring

theorem dotBase_foldl (xs : List F) (ws : List EF) (d : EF) (h : xs.length ≤ ws.length) :
    toSpec ((xs.zip ws).foldl (fun d (x, w) ↦ d + smul x w) d) = toSpec d +
      ∑ i ∈ Finset.range xs.length, algebraMap F (Spec EF) (xs.getD i 0) * toSpec (ws.getD i 0) := by
  induction xs generalizing ws d with
  | nil => simp only [List.zip_nil_left, List.foldl_nil, List.length_nil, Finset.range_zero,
      Finset.sum_empty, add_zero]
  | cons x xs ih =>
    cases ws with
    | nil => simp only [List.length_cons, List.length_nil] at h; omega
    | cons w ws =>
      simp only [List.length_cons] at h
      rw [List.zip_cons_cons, List.foldl_cons, ih ws _ (by omega), List.length_cons,
        Finset.sum_range_succ']
      simp only [toSpec_add, toSpec_smul, Algebra.smul_def, List.getD_cons_succ,
        List.getD_cons_zero]
      ring

theorem columns_foldl (alpha q : EF) (xs : List F) (ys : List EF) (a c : EF)
    (h : xs.length = ys.length) :
    toSpec ((xs.zip ys).foldl (fun (r : EF × EF) (x : F × EF) ↦
      (r.1 * alpha, r.2 + r.1 * (x.2 - Ext.ofBase x.1) * q)) (a, c)).1 =
      toSpec a * toSpec alpha ^ xs.length ∧
    toSpec ((xs.zip ys).foldl (fun (r : EF × EF) (x : F × EF) ↦
      (r.1 * alpha, r.2 + r.1 * (x.2 - Ext.ofBase x.1) * q)) (a, c)).2 =
      toSpec c + toSpec a * toSpec q * ∑ i ∈ Finset.range xs.length, toSpec alpha ^ i *
        (toSpec (ys.getD i 0) - algebraMap F (Spec EF) (xs.getD i 0)) := by
  induction xs generalizing ys a c with
  | nil => simp only [List.zip_nil_left, List.foldl_nil, List.length_nil, pow_zero, mul_one,
      Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, and_self]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil] at h; omega
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zip_cons_cons, List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih ys (a * alpha) (c + a * (y - Ext.ofBase x) * q) h
      refine ⟨?_, ?_⟩
      · rw [h1, toSpec_mul, List.length_cons, pow_succ]
        ring
      · rw [h2, List.length_cons, Finset.sum_range_succ']
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        rw [sum_pow_succ]
        simp only [toSpec_add, toSpec_mul, toSpec_sub, toSpec_ofBase']
        ring

variable {m : Type → Type} [Monad m] (H : Primitives F m)

/-- `reduceQuery` on the annotated rounds `annotate α rounds`: per matrix and point, the batched
quotient `(∑ αⁱ yᵢ - ∑ αⁱ xᵢ) / (z - x)` of the opened values `yᵢ` at `z` and the row `xᵢ` at the
query's point `x`. -/
def reduceQueryWith (P : Params) (logMax index : Nat) (rows : List (List (Array F)))
    (ann : List (List (Annotated F EF))) : M H (List (Nat × EF)) := do
  let mut ro : List (Nat × EF × EF) := []
  for (b, mats) in rows.zip ann do
    for (row, (d, pows, pts)) in b.zip mats do
      let logH := d.logSize + P.logBlowup
      let rev := reverseBits (index >>> (logMax - logH)) logH
      let x := gen * powF (twoAdicGen logH) rev
      let (ap, acc) := (ro.lookup logH).getD (1, 0)
      let mut ap := ap
      let mut acc := acc
      let D := dotBase row.toList pows.toList
      for ((z, ys), (sum, step)) in pts do
        ensure (ys.length == row.size) "opened width"
        ensure (z - Ext.ofBase x != 0) "opening point is the query point"
        let q := (z - Ext.ofBase x)⁻¹
        acc := acc + ap * q * (sum - D)
        ap := ap * step
      ro := (logH, ap, acc) :: ro.filter (·.1 != logH)
  if let some (_, acc) := ro.lookup P.logBlowup then
    ensure (acc == 0) "nonzero quotient at the blowup height"
  return (ro.mergeSort fun a b ↦ b.1 ≤ a.1).map fun (h, _, acc) ↦ (h, acc)

variable [LawfulMonad m]

theorem reduceQuery_eq (P : Params) (logMax index : Nat) (alpha : EF)
    (rows : List (List (Array F))) (rounds : List (Round F EF)) :
    reduceQuery H P logMax index alpha rows rounds =
      reduceQueryWith H P logMax index rows (annotate alpha rounds) := by
  unfold reduceQuery reduceQueryWith annotate
  simp only [List.zip_map_right, List.forIn_map, Prod.map_fst, Prod.map_snd, id_eq,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  refine congrArg (· >>= _) ?_
  congr 1
  funext ⟨b, c, mats⟩ ro
  refine congrArg (· >>= _) ?_
  congr 1
  funext ⟨row, d, pts⟩ ro
  refine congrArg (· >>= _) ?_
  dsimp only
  generalize (List.lookup (d.logSize + P.logBlowup) ro).getD (1, 0) = st
  generalize (gen : F) * powF (twoAdicGen (d.logSize + P.logBlowup))
    (reverseBits (index >>> (logMax - (d.logSize + P.logBlowup))) (d.logSize + P.logBlowup)) = x
  have hL := (le_foldl_max (fun pt : EF × List EF ↦ pt.2.length) pts 0).2
  apply forIn_congr_mem
  intro ⟨z, ys⟩ hpt ⟨a, c⟩
  apply ensure_bind_congr
  intro hlen
  apply ensure_bind_congr
  intro _
  simp only [beq_iff_eq] at hlen
  have hrow : row.toList.length = ys.length := by rw [Array.length_toList, hlen]
  obtain ⟨e1, e2⟩ := columns_foldl alpha (z - Ext.ofBase x)⁻¹ row.toList ys a c hrow
  obtain ⟨s1, s2⟩ := powSum_foldl alpha ys 0 1
  have hd := dotBase_foldl row.toList (powersFrom alpha
    (pts.foldl (fun l x ↦ max l x.2.length) 0) 1) 0 (by
      rw [length_powersFrom, hrow]; exact hL _ hpt)
  congr 2
  refine Prod.ext (toSpec_injective ?_) (toSpec_injective ?_)
  · rw [e1, toSpec_mul, powSum, s2, toSpec_one, one_mul, hrow]
  · rw [e2, toSpec_add, toSpec_mul, toSpec_mul, toSpec_sub, powSum, s1, dotBase, hd]
    simp only [toSpec_zero, toSpec_one, zero_add, one_mul]
    rw [hrow, ← Finset.sum_sub_distrib]
    refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_))
    have hi' : i < pts.foldl (fun l x ↦ max l x.2.length) 0 :=
      lt_of_lt_of_le (Finset.mem_range.mp hi) (hL _ hpt)
    rw [toSpec_getD_powersFrom alpha _ 1 i hi', toSpec_one, one_mul]
    ring

end Reduce

variable {p : ℕ} [Mont32Field p] [Poseidon2Field (FastField p)] [PackedPoseidon2 p]

local notation "F" => FastField p

/-! ### Leaf hashes in packed groups -/

/-- The Merkle leaf hashes of rows, eight at a time in packed groups (`Merkle.Packed.hashRange`)
when they have one width and fit machine indices. -/
def hashRows (xss : List (List F)) : List (Digest F) :=
  let w := (xss.headD []).length
  let n := xss.length
  if xss.all (·.length == w) && 4 * (n * w) < USize.size && 4 * (8 * n) < USize.size then
    let D := Merkle.Packed.hashRange p
      (CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields xss.flatten.toArray) w 0 n
    (List.range n).map fun r ↦ Vector.ofFn fun j ↦ word D (8 * r + j.val)
  else xss.map (Hash.Poseidon2.hash F)

/-- `hashRows` hashes every row. -/
theorem hashRows_eq (xss : List (List F)) : hashRows xss = xss.map (Hash.Poseidon2.hash F) := by
  unfold hashRows
  dsimp only
  split
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨hall, hu⟩, ho⟩ := hc
    set w := (xss.headD []).length
    set n := xss.length
    have hM : (0 + n) * w ≤ xss.flatten.toArray.size := by
      rw [List.size_toArray, List.length_flatten, Nat.zero_add]
      have : (xss.map List.length).sum = n * w := by
        rw [List.map_congr_left hall, List.map_const', List.sum_replicate, smul_eq_mul]
      omega
    have hsz : xss.flatten.toArray.size = n * w := by
      rw [List.size_toArray, List.length_flatten, List.map_congr_left hall, List.map_const',
        List.sum_replicate, smul_eq_mul]
    obtain ⟨D, hD, hs, hg⟩ := Merkle.Packed.hashRange_encode (p := p) xss.flatten.toArray w 0 n hM
      (by rw [hsz]; exact hu) ho
    rw [CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq, hD]
    apply List.ext_getElem (by simp only [List.length_map, List.length_range, n])
    intro r h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_ofFn, word_encode_getD D _ (by rw [hs]; exact ho)
      (by have := USize.le_size; omega), hg r h1 j hj]
    congr 2
    simp only [Merkle.Matrix.row, Nat.zero_add]
    apply List.ext_getElem (by simp only [List.length_map, List.length_range, hall _
      (List.getElem_mem h1)])
    intro k k1 k2
    simp only [List.length_map, List.length_range] at k1
    rw [List.getElem_map, List.getElem_range, getD_flatten_uniform 0 xss w hall r k h1 k1,
      List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ k2]
  · rfl

/-! ### Merkle multi-openings -/

/-- `Merkle.verifyMultiM` on Plonky3's Poseidon2 hashes, the leaves hashed by `hashRows`. -/
def verifyMulti (cap : List (Digest F)) (capHeight : Nat) (dims : List (Nat × Nat))
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Digest F)) : Bool :=
  match Merkle.heightGroups (dims.map (·.1)) with
  | [] => false
  | (maxH, tallest) :: rest =>
    let padded := maxH.nextPowerOfTwo
    let (levels, h) := Merkle.capLevels maxH capHeight
    if Merkle.multiShapeOk dims maxH levels indices rows sibs && cap.length == 2 ^ h &&
        rest.all (fun g ↦ 2 ^ h ≤ g.1.nextPowerOfTwo) then
      let fr := Merkle.frontier indices
      let ds := hashRows (fr.map fun (_, q) ↦ tallest.flatMap fun k ↦ (rows.getD q []).getD k [])
      let leaves := (fr.zip ds).map fun ((i, q), x) ↦ (i, q, x)
      let (top, _) := (Merkle.walkM (m := Id) (fun xs ↦ pure (Hash.Poseidon2.hash F xs))
        (fun a b ↦ pure (Hash.Poseidon2.compress F a b)) rows levels rest padded leaves sibs).run
      top.all fun (j, _, x) ↦ x == cap.getD j 0
    else false

theorem mapM_id {α β : Type} (f : α → Id β) (l : List α) :
    l.mapM f = pure (l.map fun x ↦ (f x).run) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.mapM_cons, ih]; rfl

theorem zip_map_self {α β : Type} (l : List α) (f : α → β) :
    l.zip (l.map f) = l.map fun a ↦ (a, f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.zip_cons_cons, ih, List.map_cons]

/-- `verifyMulti` is `Merkle.verifyMultiM` on Plonky3's Poseidon2 hashes. -/
theorem verifyMultiM_eq (cap : List (Digest F)) (capHeight : Nat) (dims : List (Nat × Nat))
    (indices : List Nat) (rows : List (List (List F))) (sibs : List (Digest F)) :
    Merkle.verifyMultiM (m := Id) (fun xs ↦ pure (Hash.Poseidon2.hash F xs))
      (fun a b ↦ pure (Hash.Poseidon2.compress F a b)) cap capHeight dims indices rows sibs =
      pure (verifyMulti cap capHeight dims indices rows sibs) := by
  unfold Merkle.verifyMultiM verifyMulti
  cases Merkle.heightGroups (dims.map (·.1)) with
  | nil => rfl
  | cons g rest =>
    obtain ⟨maxH, tallest⟩ := g
    dsimp only
    cases Merkle.capLevels maxH capHeight
    dsimp only
    split_ifs
    · rw [mapM_id, hashRows_eq, List.map_map, zip_map_self, List.map_map]
      rfl
    · rfl

/-! ### The verifier -/

section Verifier

variable [Mont32BaseField p] {EF : Type} [Challenge (FastField p) EF]

local notation "H" => poseidon2 (FastField p)

/-- `checkMulti` on Plonky3's Poseidon2 hashes, by `verifyMulti`. -/
def checkMultiFast (capHeight : Nat) (commit : Cap F) (dims : List (Nat × Nat))
    (indices : List Nat) (rows : List (List (List F))) (siblings : List (Digest F)) : M H Bool :=
  pure (verifyMulti commit.toList capHeight dims indices rows siblings)

theorem checkMulti_eq (capHeight : Nat) (commit : Cap F) (dims : List (Nat × Nat))
    (indices : List Nat) (rows : List (List (List F))) (siblings : List (Digest F)) :
    checkMulti H capHeight commit dims indices rows siblings =
      checkMultiFast capHeight commit dims indices rows siblings := by
  unfold checkMulti checkMultiFast
  erw [verifyMultiM_eq]
  rfl

/-- `verifyInputs` by `checkMultiFast`. -/
def verifyInputsFast (P : Params) (logMax : Nat) (indices : List Nat)
    (inputs : List (MultiOpening F)) (rounds : List (Round F EF)) : M H Unit := do
  ensure (inputs.length == rounds.length) "input batches"
  for (b, (commit, mats)) in inputs.zip rounds do
    ensure (b.values.size == indices.length) "input queries"
    ensure (b.values.all (·.size == mats.length)) "input rows"
    ensure (mats.all (!·.2.isEmpty)) "matrix without opening points"
    let dims := mats.map fun (d, pts) ↦
      (2 ^ (d.logSize + P.logBlowup), (pts.headD default).2.length)
    let logBatch := (mats.map (·.1.logSize + P.logBlowup)).foldl max 0
    ensure (← checkMultiFast P.capHeight commit dims (indices.map (· >>> (logMax - logBatch)))
      (b.values.toList.map fun r ↦ r.toList.map (·.toList)) b.siblings.toList) "input opening"

theorem verifyInputs_eq (P : Params) (logMax : Nat) (indices : List Nat)
    (inputs : List (MultiOpening F)) (rounds : List (Round F EF)) :
    verifyInputs H P logMax indices inputs rounds =
      verifyInputsFast P logMax indices inputs rounds := by
  unfold verifyInputs verifyInputsFast
  simp only [checkMulti_eq]

/-- `verifyFri` by `verifyInputsFast`, `checkMultiFast` and `reduceQueryWith` on the rounds
annotated once. -/
def verifyFriFast (P : Params) (proof : FriProof F EF) (rounds : List (Round F EF)) (alpha : EF) :
    M H Unit := do
  ensure (0 < P.numQueries && 0 < P.logBlowup && 0 < P.maxLogArity) "parameters"
  ensure (rounds.any (!·.2.isEmpty)) "no committed matrices"
  let heights := ((rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
    (fun a b ↦ b ≤ a) |>.dedup
  let logMax := heights.headD 0
  ensure (logMax ≤ twoAdicity F) "largest height"
  let logFinal := P.logBlowup + P.logFinalPolyLen
  let arities := foldSchedule P.maxLogArity logFinal logMax heights
  ensure (proof.folds.size == arities.length) "fold openings"
  ensure ((proof.folds.toList.zip arities).all fun (o, la) ↦
    o.siblings.size == P.numQueries && o.siblings.all (·.size == 2 ^ la - 1)) "fold siblings"
  ensure (P.commitPowBits != 0 || proof.commitWitnesses.all (· == 0)) "commit witnesses"
  ensure (P.queryPowBits != 0 || proof.queryWitness == 0) "query witness"
  ensure (proof.finalPoly.size == 2 ^ P.logFinalPolyLen) "final polynomial length"
  observeList H (DomainSeparator.friSeed F EF arities (2 ^ P.logFinalPolyLen) P.commitPowBits
    P.queryPowBits P.numQueries logMax P.logBlowup P.maxLogArity)
  ensure (proof.commits.size == arities.length &&
    proof.commitWitnesses.size == arities.length && proof.commits.all (·.size != 0))
    "commit rounds"
  let mut betas := #[]
  for (c, w) in proof.commits.toList.zip proof.commitWitnesses.toList do
    observeCap H c
    ensure (← checkWitness H P.commitPowBits w) "commit witness"
    betas := betas.push (← sampleExt H : EF)
  observeExts H proof.finalPoly.toList
  ensure (← checkWitness H P.queryPowBits proof.queryWitness) "query witness"
  let indices ← (List.range P.numQueries).mapM fun _ ↦ sampleBits H logMax
  verifyInputsFast P logMax indices proof.inputs.toList rounds
  let ann := annotate alpha rounds
  let groups ← indices.zipIdx.mapM fun (index, q) ↦ do
    let ro ← reduceQueryWith H P logMax index
      (proof.inputs.toList.map fun b ↦ (b.values.getD q #[]).toList) ann
    let (eval, index, gs) ← foldQuery H P logMax index q betas.toList arities proof.folds.toList ro
    let x := Ext.ofBase (powF (twoAdicGen logMax) (reverseBits index logMax))
    let expected := proof.finalPoly.foldr (fun c acc ↦ acc * x + c) 0
    ensure (expected == eval) "final polynomial mismatch"
    return gs
  let mut logH := logMax
  for ((c, o), (la, i)) in (proof.commits.toList.zip proof.folds.toList).zip arities.zipIdx do
    let logFolded := logH - la
    let gs := groups.map fun g ↦ g.getD i (0, [])
    ensure (← checkMultiFast P.capHeight c [(2 ^ logFolded, Challenge.d EF * 2 ^ la)]
      (gs.map (·.1)) (gs.map fun (_, evals) ↦ [evals.flatMap Ext.coeffs]) o.path.toList)
      "commit-phase opening"
    logH := logFolded

theorem verifyFri_eq (P : Params) (proof : FriProof F EF) (rounds : List (Round F EF))
    (alpha : EF) : verifyFri H P proof rounds alpha = verifyFriFast P proof rounds alpha := by
  unfold verifyFri verifyFriFast
  simp only [checkMulti_eq, verifyInputs_eq, reduceQuery_eq]

/-- `verifyPcs` by `verifyFriFast`. -/
def verifyPcsFast (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF) :
    M H Unit := do
  ensure (P.batchPowBits != 0 || proof.batchWitness == 0) "batch witness"
  observeList H (DomainSeparator.pcsSeed F EF (claimCounts rounds) P.batchPowBits)
  for (_, mats) in rounds do
    for (_, pts) in mats do
      for (_, ys) in pts do
        observeExts H ys
  ensure (← checkWitness H P.batchPowBits proof.batchWitness) "batch witness"
  let alpha ← sampleExt H
  verifyFriFast P proof rounds alpha

theorem verifyPcs_eq (P : Params) (rounds : List (Round F EF)) (proof : FriProof F EF) :
    verifyPcs H P rounds proof = verifyPcsFast P rounds proof := by
  unfold verifyPcs verifyPcsFast
  simp only [verifyFri_eq]

/-- Plonky3's verifier `verify`, by `verifyPcsFast` (`verifyFast_eq`). -/
def verifyFast (P : Params) (A : Air F) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (pis : List F) : Except String Unit := Id.run <| ExceptT.run do
  let db := proof.degreeBits
  let logChunks := A.logQuotientChunks db
  let ds := chunkDomains db logChunks
  let o := proof.opened
  unless db + logChunks ≤ twoAdicity F do
    throw "degree bits"
  unless A.periodicFits db do
    throw "periodic columns"
  unless pis.length == A.numPublicValues do
    throw "public values"
  unless o.traceLocal.size == A.width && traceNextOk A o &&
      o.quotientChunks.size == 2 ^ logChunks &&
      o.quotientChunks.all (·.size == Challenge.d EF) && preprocessedShapeOk A vk o db do
    throw "invalid proof shape"
  unless P.oodPowBits != 0 || proof.oodWitness == 0 do
    throw "out-of-domain witness"
  unless proof.quotientCommit.size != 0 do
    throw "empty quotient commitment"
  let run : M H (EF × EF) := do
    observeList H (starkSeedOf EF P A db)
    observeCap H proof.traceCommit
    observeList H (preprocessedDigest vk)
    observeList H pis
    let alpha ← sampleExt H
    observeCap H proof.quotientCommit
    ensure (← checkWitness H P.oodPowBits proof.oodWitness) "out-of-domain witness"
    let zeta ← sampleExt H
    ensure (Ext.powTwo zeta db - 1 != 0) "out-of-domain point in the trace domain"
    verifyPcsFast P (openingRounds A vk proof zeta) proof.fri
    return (alpha, zeta)
  let ((alpha, zeta), _) ← run.run (poseidon2 (FastField p)).init
  let quotient := recompose ds o.quotientChunks.toList zeta
  unless checkConstraints A pis o db zeta alpha quotient do
    throw "out-of-domain evaluation mismatch"

/-- **The fast verifier is Plonky3's verifier.** -/
theorem verifyFast_eq (P : Params) (A : Air F) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (pis : List F) : verifyFast P A vk proof pis = verify P A vk proof pis := by
  unfold verifyFast verify verifyWith
  simp only [verifyPcs_eq]
  rfl

end Verifier

end CompStark.Stark.Fast
