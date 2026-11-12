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
    (vals : S.BoundaryValues L) (z : List E)
    (hvals : ∀ t c, S.Direct L t = true → (∃ I ∈ (S.table t).interactions, Expr.cur c ∈ I.tuple) →
      S.boundaryValue L vals t c = S.column L w t c z)
    (b : Block S.tables.length)
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
      exact ((hvals t' c hd ⟨I, hI t' I rfl, hc⟩).trans rfl).symm
    · intro t' c hbI
      subst hbI
      simp only [Direct, Bool.and_eq_true, List.isEmpty_iff] at hd
      have h2 : (S.table t').nonzero = [] := hd.1.1.2
      have := hb t' c rfl
      rw [h2] at this
      cases this
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, zero_add]
    ring

end CompStark.Tables.System
