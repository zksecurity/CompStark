/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.Bus.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.BusOutput

/-! A side's leaf extension is its public part plus its table debt (`leaf_decomposition`). -/

@[expose] public section

namespace CompStark.Tables.System

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear

/-- An expression that reads no preprocessed column ignores the preprocessed values. -/
theorem eval_envE_prep (e : Expr K) (w : ℕ) (he : e.colsBelow w 0 0 0 = true) (v p p' : ℕ → E) :
    e.eval (envE v p) = e.eval (envE v p') := by
  induction e with
  | prepCur c => simp [Expr.colsBelow] at he
  | prepNext c => simp [Expr.colsBelow] at he
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [Expr.colsBelow, Bool.and_eq_true] at he
    simp only [Expr.eval, ha he.1, hb he.2]
  | _ => rfl

/-- An atomic expression's evaluation is affine: its extension over rows is its evaluation at the
columns' extensions. -/
theorem mle_eval_atomic (n : ℕ) (e : Expr K) (he : e.atomic = true) (v p : ℕ → ℕ → E) (z : List E) :
    mle n (fun i ↦ e.eval (envE (v i) (p i))) z =
      e.eval (envE (fun c ↦ mle n (fun i ↦ v i c) z) (fun c ↦ mle n (fun i ↦ p i c) z)) := by
  cases e with
  | cur c | prepCur c => rfl
  | const c => exact mle_const n _ z
  | _ => simp [Expr.atomic] at he

variable (S : System K) (k : ℕ) (α : Fin k → E) (β : E)

/-- A block of atomic tuples has an affine form: its extension over rows is its form at the
columns' extensions. -/
theorem mle_formE_atomic (n : ℕ) (b : Block S.tables.length)
    (hatomic : ∀ t I, b = .interaction t I → ∀ e ∈ I.tuple, e.atomic = true)
    (v p : ℕ → ℕ → E) (z : List E) :
    mle n (fun i ↦ S.formE k α β b (v i) (p i)) z =
      S.formE k α β b (fun c ↦ mle n (fun i ↦ v i c) z) (fun c ↦ mle n (fun i ↦ p i c) z) := by
  cases b with
  | nonzero t c => rfl
  | interaction t I =>
    simp only [formE, fingerprintE]
    rw [mle_sub, mle_const, mle_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show (fun i ↦ encodeE k (S.busIndex I.bus) (I.tuple.map (Expr.eval (envE (v i) (p i)))) j *
        ∏ x : Fin k, eqFactor (α x) (bit j.val x.val)) = fun i ↦
          (∏ x : Fin k, eqFactor (α x) (bit j.val x.val)) *
            encodeE k (S.busIndex I.bus) (I.tuple.map (Expr.eval (envE (v i) (p i)))) j from
      funext fun i ↦ mul_comm _ _, mle_smul, mul_comm]
    congr 1
    simp only [encodeE]
    by_cases h0 : j.val = 0
    · simp only [h0, List.getD_cons_zero]
      exact mle_const n _ z
    · obtain ⟨m, hm⟩ : ∃ m, j.val = m + 1 := ⟨j.val - 1, by omega⟩
      simp only [hm, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
      by_cases hl : m < I.tuple.length
      · simp only [List.getElem?_eq_getElem hl, Option.map_some, Option.getD_some]
        exact mle_eval_atomic n _ (hatomic t I rfl _ (List.getElem_mem hl)) v p z
      · simp only [List.getElem?_eq_none (show I.tuple.length ≤ m by omega), Option.map_none,
          Option.getD_none]
        exact mle_const n _ z

variable (L : Layout S.tables.length) (w : Witness K S.tables.length)

/-- The challenge-field values of row `i` of table `t`. -/
def rowE (t : Fin S.tables.length) (i : ℕ) : ℕ → E := fun c ↦ ofK (((w t).getD i #[]).getD c 0)

/-- The challenge-field preprocessed values of row `i` of table `t`. -/
def prepE (t : Fin S.tables.length) (i : ℕ) : ℕ → E :=
  fun c ↦ ofK ((S.table t).air.preprocessed.getD (i * (S.table t).air.preprocessedWidth + c) 0)

/-- A form reads its committed values only at the columns its tuples read. -/
theorem formE_congr (b : Block S.tables.length) (v v' p : ℕ → E)
    (hatomic : ∀ t I, b = .interaction t I → ∀ e ∈ I.tuple, e.atomic = true)
    (hv : ∀ t I, b = .interaction t I → ∀ c, Expr.cur c ∈ I.tuple → v c = v' c)
    (hnz : ∀ t c, b = .nonzero t c → v c = v' c) :
    S.formE k α β b v p = S.formE k α β b v' p := by
  cases b with
  | nonzero t c => exact hnz t c rfl
  | interaction t I =>
    have hl : I.tuple.map (Expr.eval (envE v p)) = I.tuple.map (Expr.eval (envE v' p)) := by
      apply List.map_congr_left
      intro e he
      have ha := hatomic t I rfl e he
      cases e with
      | cur c => exact hv t I rfl c he
      | prepCur c | const c => rfl
      | _ => simp [Expr.atomic] at ha
    simp only [formE, hl]

/-- A function that vanishes on the Boolean rows has zero extension. -/
theorem mle_zero_of_rows (n : ℕ) (f : ℕ → E) (hf : ∀ i < 2 ^ n, f i = 0) (z : List E) :
    mle n f z = 0 := by
  rw [show mle n f z = mle n (fun _ ↦ 0) z from by
    unfold mle
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hf i i.isLt], mle_const]

/-- A block's leaf extension is its public part plus, for a table that is not opened directly,
its form's extension. -/
theorem mle_blockLeaf (hT : ∀ t, (S.table t).WellFormed)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t)
    (hpad : ∀ t, L.executed t < 2 ^ L.logHeight t → ∀ I ∈ (S.table t).interactions, ∀ e ∈ I.tuple,
      e.colsBelow (S.table t).air.width 0 0 0 = true)
    (vals : S.BoundaryValues L) (z : List E) (b : Block S.tables.length)
    (hvals : ∀ c, S.Direct L (Block.table S b) = true →
      (∃ I ∈ (S.table (Block.table S b)).interactions, Expr.cur c ∈ I.tuple) →
      S.boundaryValue L vals (Block.table S b) c = S.column L w (Block.table S b) c z)
    (hb : ∀ t c, b = .nonzero t c → c ∈ (S.table t).nonzero)
    (hI : ∀ t I, b = .interaction t I → I ∈ (S.table t).interactions) :
    mle (Block.height S L b) (S.blockLeaf L k w α β b) z =
      S.blockPublic L k α β vals b z +
        if S.Direct L (Block.table S b) then 0 else
          mle (Block.height S L b) (fun i ↦ S.formE k α β b (S.rowE w (Block.table S b) i)
            (S.prepE (Block.table S b) i)) z := by
  set t := Block.table S b with ht
  have hh : Block.height S L b = L.logHeight t := by cases b <;> rfl
  have hlocal : ∀ t' I, b = .interaction t' I → ∀ e ∈ I.tuple, e.currentRow = true := by
    intro t' I hbI e he
    subst hbI
    exact ((hT t').2.2.2.2.1 I (hI t' I rfl) e he).1
  have hform : ∀ i, S.blockForm k α β b (S.env L w t i) (fun c ↦ ((w t).getD i #[]).getD c 0) =
      S.formE k α β b (S.rowE w t i) (S.prepE t i) := fun i ↦
    S.blockForm_eq_formE k α β b _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) hlocal
  have hleaf : S.blockLeaf L k w α β b = fun i ↦ S.formE k α β b (S.rowE w t i) (S.prepE t i) +
      if L.executed t ≤ i then
        1 - S.blockForm k α β b (S.paddingEnv L t i) (fun c ↦ (S.table t).padding.getD c 0)
      else 0 := by
    funext i
    simp only [blockLeaf, ← ht, hform]
  rw [hleaf, mle_add, hh]
  -- The padding term is the public correction.
  have hpadTerm : mle (L.logHeight t) (fun i ↦ if L.executed t ≤ i then
        1 - S.blockForm k α β b (S.paddingEnv L t i) (fun c ↦ (S.table t).padding.getD c 0)
      else 0) z =
      (1 - S.formE k α β b (fun c ↦ ofK ((S.table t).padding.getD c 0)) (fun _ ↦ 0)) *
        S.paddingMass L t z := by
    by_cases hp : L.executed t < 2 ^ L.logHeight t
    · have hconst : ∀ i, S.blockForm k α β b (S.paddingEnv L t i) (fun c ↦ (S.table t).padding.getD c 0) =
          S.formE k α β b (fun c ↦ ofK ((S.table t).padding.getD c 0)) (fun _ ↦ 0) := by
        intro i
        rw [S.blockForm_eq_formE k α β b (S.paddingEnv L t i) (fun c ↦ (S.table t).padding.getD c 0)
          (fun _ ↦ rfl) (fun _ ↦ rfl) hlocal]
        cases b with
        | nonzero => rfl
        | interaction t' I =>
          have hl : I.tuple.map (Expr.eval (envE (fun c ↦ ofK ((S.table t).padding.getD c 0))
                (fun c ↦ ofK ((S.paddingEnv L t i).prepCur c)))) =
              I.tuple.map (Expr.eval (envE (fun c ↦ ofK ((S.table t).padding.getD c 0)) fun _ ↦ 0)) :=
            List.map_congr_left fun e he ↦ eval_envE_prep e _ (hpad t' hp I (hI t' I rfl) e he) _ _ _
          simp only [formE, hl]
      simp only [hconst]
      rw [paddingMass, ← mle_smul]
      congr 1
      funext i
      split <;> simp
    · have hfull : L.executed t = 2 ^ L.logHeight t := le_antisymm (hexec t) (Nat.not_lt.mp hp)
      rw [mle_zero_of_rows _ _ (fun i hi ↦ by simp only [hfull, show ¬ 2 ^ L.logHeight t ≤ i by omega,
        ↓reduceIte]), paddingMass, mle_zero_of_rows _ _ (fun i hi ↦ by
          simp only [hfull, show ¬ 2 ^ L.logHeight t ≤ i by omega, ↓reduceIte]), mul_zero]
  rw [hpadTerm, blockPublic, ← ht]
  by_cases hd : S.Direct L t = true
  · simp only [hd, ↓reduceIte, add_zero]
    have hatomic : ∀ t' I, b = .interaction t' I → ∀ e ∈ I.tuple, e.atomic = true := by
      intro t' I hbI e he
      subst hbI
      simp only [Direct, Bool.and_eq_true, List.all_eq_true] at hd
      exact hd.2 I (hI t' I rfl) e he
    rw [S.mle_formE_atomic k α β _ b hatomic]
    have hprep : (fun c ↦ mle (L.logHeight t) (fun i ↦ S.prepE t i c) z) = fun c ↦ S.prepColumn L t c z :=
      rfl
    rw [hprep]
    refine congrArg (· + _) ?_
    apply S.formE_congr k α β b _ _ _ hatomic
    · intro t' I hbI c hc
      subst hbI
      exact ((hvals c hd ⟨I, hI t' I rfl, hc⟩).trans rfl).symm
    · intro t' c hbI
      subst hbI
      simp only [Direct, Bool.and_eq_true, List.isEmpty_iff] at hd
      have h2 : (S.table t').nonzero = [] := hd.1.1.2
      have := hb t' c rfl
      rw [h2] at this
      cases this
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, zero_add]
    ring

/-- The table debt is the selector-weighted sum of the other tables' blocks' form extensions. -/
theorem tableDebt_eq (μ : ℕ) (side : Fin 3) (ζ : List E) :
    S.tableDebt L k α β μ w side ζ =
      S.sumBlocks L μ ζ (fun b ↦ if S.Direct L (Block.table S b) then 0 else
        mle (Block.height S L b) (fun i ↦ S.formE k α β b (S.rowE w (Block.table S b) i)
          (S.prepE (Block.table S b) i)) (ζ.take (Block.height S L b))) (S.sortedBlocks L side) 0 := by
  set bs := S.sortedBlocks L side
  have hh : ∀ b : Block S.tables.length, Block.height S L b = L.logHeight (Block.table S b) := by
    intro b; cases b <;> rfl
  unfold tableDebt tableForm
  simp only [sumBlocks_eq_sum, Nat.zero_add]
  have inner : ∀ t : Fin S.tables.length,
      mle (L.logHeight t) (fun i ↦ ∑ j : Fin bs.length,
        selectorWeight μ (Block.height S L bs[j]) (S.blockOffset L bs j.val) ζ *
          (if Block.table S bs[j] = t then S.formE k α β bs[j] (S.rowE w t i) (S.prepE t i) else 0))
        (ζ.take (L.logHeight t)) =
      ∑ j : Fin bs.length, selectorWeight μ (Block.height S L bs[j]) (S.blockOffset L bs j.val) ζ *
        (if Block.table S bs[j] = t then
          mle (L.logHeight t) (fun i ↦ S.formE k α β bs[j] (S.rowE w t i) (S.prepE t i))
            (ζ.take (L.logHeight t)) else 0) := by
    intro t
    rw [mle_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mle_smul]
    congr 1
    split
    · rfl
    · exact mle_const _ _ _
  have collapse : ∀ (c : Fin S.tables.length) (f : Fin S.tables.length → E),
      (∑ t : Fin S.tables.length, if S.Direct L t = true then 0 else if c = t then f t else 0) =
        if S.Direct L c = true then 0 else f c := by
    intro c f
    rw [show (fun t ↦ if S.Direct L t = true then 0 else if c = t then f t else 0) =
        fun t ↦ if c = t then (if S.Direct L t = true then 0 else f t) else 0 from
      funext fun t ↦ by by_cases h : c = t <;> simp [h]]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ c)]
  calc (∑ t : Fin S.tables.length, if S.Direct L t = true then 0 else
        mle (L.logHeight t) (fun i ↦ ∑ j : Fin bs.length,
          selectorWeight μ (Block.height S L bs[j]) (S.blockOffset L bs j.val) ζ *
            (if Block.table S bs[j] = t then S.formE k α β bs[j] (S.rowE w t i) (S.prepE t i) else 0))
          (ζ.take (L.logHeight t)))
      = ∑ t : Fin S.tables.length, ∑ j : Fin bs.length,
          selectorWeight μ (Block.height S L bs[j]) (S.blockOffset L bs j.val) ζ *
            (if S.Direct L t = true then 0 else if Block.table S bs[j] = t then
              mle (L.logHeight t) (fun i ↦ S.formE k α β bs[j] (S.rowE w t i) (S.prepE t i))
                (ζ.take (L.logHeight t)) else 0) := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases hd : S.Direct L t = true
        · simp only [hd, ↓reduceIte, mul_zero, Finset.sum_const_zero]
        · simp only [hd, Bool.false_eq_true, ↓reduceIte]
          exact inner t
    _ = ∑ j : Fin bs.length, selectorWeight μ (Block.height S L bs[j]) (S.blockOffset L bs j.val) ζ *
          (if S.Direct L (Block.table S bs[j]) = true then 0 else
            mle (Block.height S L bs[j]) (fun i ↦ S.formE k α β bs[j]
              (S.rowE w (Block.table S bs[j]) i) (S.prepE (Block.table S bs[j]) i))
              (ζ.take (Block.height S L bs[j]))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum, collapse, hh]

omit k α β w in
/-- Block sums are additive. -/
theorem sumBlocks_add (μ : ℕ) (ζ : List E) (f g : Block S.tables.length → E)
    (bs : List (Block S.tables.length)) (offset : ℕ) :
    S.sumBlocks L μ ζ (fun b ↦ f b + g b) bs offset =
      S.sumBlocks L μ ζ f bs offset + S.sumBlocks L μ ζ g bs offset := by
  induction bs generalizing offset with
  | nil => simp only [sumBlocks, add_zero]
  | cons b bs ih => simp only [sumBlocks, ih]; ring

omit k α β w in
/-- Block sums depend only on their members' values. -/
theorem sumBlocks_congr (μ : ℕ) (ζ : List E) (f g : Block S.tables.length → E)
    (bs : List (Block S.tables.length)) (offset : ℕ) (h : ∀ b ∈ bs, f b = g b) :
    S.sumBlocks L μ ζ f bs offset = S.sumBlocks L μ ζ g bs offset := by
  induction bs generalizing offset with
  | nil => rfl
  | cons b bs ih =>
    simp only [sumBlocks, h b (List.mem_cons_self ..),
      ih _ fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]

/-- A side's leaf extension is its public part, at the true boundary values, plus its table
debt. -/
theorem leaf_decomposition (hT : ∀ t, (S.table t).WellFormed)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t)
    (hpad : ∀ t, L.executed t < 2 ^ L.logHeight t → ∀ I ∈ (S.table t).interactions, ∀ e ∈ I.tuple,
      e.colsBelow (S.table t).air.width 0 0 0 = true)
    (μ : ℕ) (fits : S.Fits L μ) (side : Fin 3) (z : Vector E μ) (vals : S.BoundaryValues L)
    (hvals : ∀ t c, S.Direct L t = true → (∃ I ∈ (S.table t).interactions, Expr.cur c ∈ I.tuple) →
      S.boundaryValue L vals t c = S.column L w t c (z.toList.take (L.logHeight t))) :
    mle μ (S.leaves L k w α β side) z.toList =
      S.publicPart L k α β μ vals side z.toList + S.tableDebt L k α β μ w side z.toList := by
  have hh : ∀ b : Block S.tables.length, Block.height S L b = L.logHeight (Block.table S b) := by
    intro b; cases b <;> rfl
  have mem : ∀ b ∈ S.sortedBlocks L side, (∀ t c, b = .nonzero t c → c ∈ (S.table t).nonzero) ∧
      ∀ t I, b = .interaction t I → I ∈ (S.table t).interactions := by
    intro b hb
    have hb' := (List.mergeSort_perm (S.blocks side) _).mem_iff.mp hb
    simp only [blocks, List.mem_flatMap, List.mem_finRange, true_and] at hb'
    obtain ⟨t, ht⟩ := hb'
    split at ht
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
      refine ⟨fun t' c' (h : Block.nonzero t c = .nonzero t' c') ↦ ?_,
        fun t' I' (h : Block.nonzero t c = .interaction t' I') ↦ by cases h⟩
      cases h
      exact hc
    · obtain ⟨I, hI, rfl⟩ := List.mem_map.mp ht
      refine ⟨fun t' c' (h : Block.interaction t I = .nonzero t' c') ↦ (by cases h),
        fun t' I' (h : Block.interaction t I = .interaction t' I') ↦ ?_⟩
      cases h
      exact (List.mem_filter.mp hI).1
  rw [S.leaves_blocks L k w α β μ fits side z, tableDebt_eq, publicPart]
  rw [S.sumBlocks_congr L μ z.toList _ _ _ 0 (fun b hb ↦ S.mle_blockLeaf k α β L w hT hexec hpad vals
    (z.toList.take (Block.height S L b)) b
    (fun c hd hr ↦ (hvals (Block.table S b) c hd hr).trans (by rw [hh]))
    (mem b hb).1 (mem b hb).2)]
  rw [sumBlocks_add]
  ring

end CompStark.Tables.System
