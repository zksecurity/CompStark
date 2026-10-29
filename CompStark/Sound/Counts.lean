/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.Inclusion

/-! # Checking an AIR's count weights

An AIR owes the verifier its count weights: on every row of a satisfying trace, the magnitudes of
its queries' multiplicities sum to at most its weights (`Air.CountsBounded`). `Air.countsChecked`
checks it syntactically, and `countsBounded_of_countsChecked` proves the check sound for any AIR,
so a concrete AIR discharges the obligation by `decide`.

The check bounds each query's multiplicity by `Expr.countBound`, a bound on the magnitude of the
integer an expression stands for on every row, as LogUp's generation evaluates it
(`generationRow`): `1` for the row selectors, which it reads as `0` or `1`; `1` for a boolean
column at either row; `k` for a constant `±k`, `k` the smaller of the constant's canonical value
and its complement; and sums and products of bounds for sums, differences and products. A column
is boolean (`Air.isBoolean`) when the AIR asserts `x (x - 1)` for it (Plonky3's `assert_bool`) on
every row, or on transitions (`when_transition`) and on the last row (`when_last_row`): the
transition selector vanishes on the last row, so a transition constraint alone leaves the last
row free. Every lookup's query bounds must sum to at most its count weight.
-/

@[expose] public section
namespace CompStark.Stark

variable {F : Type}

/-- `e` asserts that column `j` is boolean: it is `x (x - 1)`, `x` the column at the current row
(Plonky3's `assert_bool`). -/
def Expr.isBoolCheck [DecidableEq F] [One F] (j : Nat) : Expr F → Bool
  | .mul (.cur a) (.sub (.cur b) (.const c)) => a == j && b == j && decide (c = 1)
  | _ => false

/-- `e` asserts that column `j` is boolean on transitions (`isBoolCheck` under
`when_transition`). -/
def Expr.isTransitionBoolCheck [DecidableEq F] [One F] (j : Nat) : Expr F → Bool
  | .mul .isTransition e => e.isBoolCheck j
  | _ => false

/-- `e` asserts that column `j` is boolean on the last row (`isBoolCheck` under `when_last_row`). -/
def Expr.isLastRowBoolCheck [DecidableEq F] [One F] (j : Nat) : Expr F → Bool
  | .mul .isLastRow e => e.isBoolCheck j
  | _ => false

/-- Column `j` is boolean on every row: the AIR asserts it on every row, or on transitions and on
the last row. -/
def Air.isBoolean [DecidableEq F] [One F] (A : Air F) (j : Nat) : Bool :=
  A.constraints.any (·.isBoolCheck j) ||
    (A.constraints.any (·.isTransitionBoolCheck j) && A.constraints.any (·.isLastRowBoolCheck j))

section Check
variable [BaseField F]

/-- A bound `k` on the magnitude of the integer the constant `c` stands for, if `c` is `k` or
`-k`, `k` the smaller of its canonical value and its complement. -/
def constBound (c : F) : Option Nat :=
  let v := CompPoly.CanonicalNat.toNat c
  let k := min v (CompPoly.CanonicalNat.bound F - v)
  if c = (k : F) ∨ c = -(k : F) then some k else none

/-- A bound on the magnitude of the integer `e` stands for on every row of every trace satisfying
`A`, as LogUp's generation evaluates it (`generationRow`), if `e` is built from row selectors,
boolean columns (`Air.isBoolean`) and constants by sums, differences and products. -/
def Expr.countBound (A : Air F) : Expr F → Option Nat
  | .cur j | .next j => if A.isBoolean j then some 1 else none
  | .const c => constBound c
  | .isFirstRow | .isLastRow | .isTransition => some 1
  | .add a b | .sub a b => (a.countBound A).bind fun x ↦ (b.countBound A).map (x + ·)
  | .mul a b => (a.countBound A).bind fun x ↦ (b.countBound A).map (x * ·)
  | .prepCur _ | .prepNext _ | .periodic _ | .pub _ => none

/-- The sum of the `countBound`s of the multiplicities of the tuples of positive weight, if each
has one. -/
def Air.queryBound (A : Air F) : List (List (Expr F) × Count F) → Option Nat
  | [] => some 0
  | t :: ts => if 0 < t.2.weight then
      (t.2.expr.countBound A).bind fun x ↦ (A.queryBound ts).map (x + ·)
    else A.queryBound ts

/-- Every lookup's queries' multiplicities have bounds (`Expr.countBound`) summing to at most its
count weight: a syntactic check of `Air.CountsBounded`. -/
def Air.countsChecked (A : Air F) : Bool :=
  A.lookups.all fun l ↦ (A.queryBound l.entries).any (· ≤ l.countWeight)

end Check

end CompStark.Stark

namespace CompStark.Sound.Batch
open CompStark.Stark CompStark.Lookup

variable {F : Type} [BaseField F]

/-! ### Boolean columns -/

theorem eq_of_isBoolCheck {j : Nat} {e : Expr F} (h : e.isBoolCheck j = true) :
    e = .mul (.cur j) (.sub (.cur j) (.const 1)) := by
  unfold Expr.isBoolCheck at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  · exact absurd h Bool.false_ne_true

theorem eq_of_isTransitionBoolCheck {j : Nat} {e : Expr F} (h : e.isTransitionBoolCheck j = true) :
    e = .mul .isTransition (.mul (.cur j) (.sub (.cur j) (.const 1))) := by
  unfold Expr.isTransitionBoolCheck at h
  split at h
  · rw [eq_of_isBoolCheck h]
  · exact absurd h Bool.false_ne_true

theorem eq_of_isLastRowBoolCheck {j : Nat} {e : Expr F} (h : e.isLastRowBoolCheck j = true) :
    e = .mul .isLastRow (.mul (.cur j) (.sub (.cur j) (.const 1))) := by
  unfold Expr.isLastRowBoolCheck at h
  split at h
  · rw [eq_of_isBoolCheck h]
  · exact absurd h Bool.false_ne_true

theorem eq_zero_or_one {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The transition selector `ωⁱ - ω⁻¹` is nonzero on every row but the last. -/
theorem transition_ne_zero {logN : Nat} (hlogN : logN ≤ twoAdicity F) {r : Nat}
    (hr : r + 1 < 2 ^ logN) : twoAdicGen (F := F) logN ^ r - (twoAdicGen logN)⁻¹ ≠ 0 := by
  have hprim := BaseField.isPrimitiveRoot_twoAdicGen (F := F) logN hlogN
  have hne := BaseField.twoAdicGen_ne_zero (F := F) logN hlogN
  intro h
  have h1 : twoAdicGen (F := F) logN ^ (r + 1) = 1 := by
    rw [pow_succ, sub_eq_zero.mp h, inv_mul_cancel₀ hne]
  have := Nat.le_of_dvd (Nat.succ_pos r) ((hprim.pow_eq_one_iff_dvd _).mp h1)
  omega

/-- A boolean column is `0` or `1` on every row of a satisfying trace of `2 ^ logN` rows. -/
theorem isBoolean_spec {A : Air F} {logN : Nat} {trace : Array F} {pv : List F}
    (hsat : A.Satisfied logN trace pv) (hlogN : logN ≤ twoAdicity F) {j : Nat}
    (hb : A.isBoolean j = true) {r : Nat} (hr : r < 2 ^ logN) :
    trace.getD (r * A.width + j) 0 = 0 ∨ trace.getD (r * A.width + j) 0 = 1 := by
  refine eq_zero_or_one ?_
  have hv := hsat.vanish
  unfold Air.isBoolean at hb
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at hb
  rcases hb with ⟨c, hc, hcb⟩ | ⟨⟨c, hc, hcb⟩, ⟨d, hd, hdb⟩⟩
  · have := hv c hc r hr
    rw [eq_of_isBoolCheck hcb] at this
    simpa only [Expr.eval, Air.traceRow] using this
  · rcases Nat.lt_or_ge (r + 1) (2 ^ logN) with hlt | hge
    · have := hv c hc r hr
      rw [eq_of_isTransitionBoolCheck hcb] at this
      simp only [Expr.eval, Air.traceRow] at this
      exact (mul_eq_zero.mp this).resolve_left (transition_ne_zero hlogN hlt)
    · have := hv d hd r hr
      rw [eq_of_isLastRowBoolCheck hdb] at this
      simp only [Expr.eval, Air.traceRow, show r + 1 = 2 ^ logN by omega, ↓reduceIte] at this
      refine (mul_eq_zero.mp this).resolve_left (mul_ne_zero ?_
        (BaseField.twoAdicGen_ne_zero logN hlogN))
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact pow_ne_zero _ BaseField.two_ne_zero

/-! ### Soundness of the bounds -/

theorem constBound_spec {c : F} {k : Nat} (h : constBound c = some k) :
    ∃ z : ℤ, (z : F) = c ∧ z.natAbs ≤ k := by
  unfold constBound at h
  dsimp only at h
  split at h
  · rename_i hc
    rw [Option.some.injEq] at h
    subst h
    rcases hc with hc | hc
    · exact ⟨_, by rw [Int.cast_natCast]; exact hc.symm, (Int.natAbs_natCast _).le⟩
    · exact ⟨-_, by rw [Int.cast_neg, Int.cast_natCast]; exact hc.symm, by
        rw [Int.natAbs_neg, Int.natAbs_natCast]⟩
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

theorem bind_map_eq_some {a b : Option Nat} {f : Nat → Nat → Nat} {k : Nat}
    (h : (a.bind fun x ↦ b.map (f x)) = some k) : ∃ x y, a = some x ∧ b = some y ∧ k = f x y := by
  cases a with
  | none => exact absurd h (by simp only [Option.bind_none, reduceCtorEq, not_false_eq_true])
  | some x =>
    cases b with
    | none => exact absurd h (by simp only [Option.bind_some, Option.map_none, reduceCtorEq,
        not_false_eq_true])
    | some y =>
      simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨x, y, rfl, rfl, h.symm⟩

/-- **The count bounds are sound.** On every row of a satisfying trace, an expression with a
`countBound` stands for an integer of at most that magnitude. -/
theorem countBound_spec {A : Air F} {logN : Nat} {trace : Array F} {pv : List F}
    (hsat : A.Satisfied logN trace pv) (hlogN : logN ≤ twoAdicity F) {r : Nat}
    (hr : r < 2 ^ logN) : ∀ (e : Expr F) (k : Nat), e.countBound A = some k →
      ∃ z : ℤ, (z : F) = e.eval (generationRow A logN trace pv r) ∧ z.natAbs ≤ k
  | .cur j, k, h | .next j, k, h => by
    unfold Expr.countBound at h
    split at h
    · rename_i hb
      rw [Option.some.injEq] at h
      subst h
      have hrow : ∀ s < 2 ^ logN, ∃ z : ℤ, (z : F) = trace.getD (s * A.width + j) 0 ∧
          z.natAbs ≤ 1 := fun s hs ↦ by
        rcases isBoolean_spec hsat hlogN hb hs with h0 | h1
        · exact ⟨0, by rw [Int.cast_zero, h0], by omega⟩
        · exact ⟨1, by rw [Int.cast_one, h1], le_rfl⟩
      first
        | exact hrow r hr
        | exact hrow _ (Nat.mod_lt _ (Nat.two_pow_pos logN))
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .const c, k, h => constBound_spec h
  | .isFirstRow, k, h | .isLastRow, k, h | .isTransition, k, h => by
    simp only [Expr.countBound, Option.some.injEq] at h
    subst h
    simp only [Expr.eval, generationRow]
    split
    · exact ⟨1, Int.cast_one, le_rfl⟩
    · exact ⟨0, Int.cast_zero, by omega⟩
  | .add a b, k, h => by
    obtain ⟨x, y, hx, hy, rfl⟩ := bind_map_eq_some h
    obtain ⟨za, ha, hza⟩ := countBound_spec hsat hlogN hr a x hx
    obtain ⟨zb, hb, hzb⟩ := countBound_spec hsat hlogN hr b y hy
    exact ⟨za + zb, by rw [Int.cast_add, ha, hb]; rfl, (Int.natAbs_add_le _ _).trans (by omega)⟩
  | .sub a b, k, h => by
    obtain ⟨x, y, hx, hy, rfl⟩ := bind_map_eq_some h
    obtain ⟨za, ha, hza⟩ := countBound_spec hsat hlogN hr a x hx
    obtain ⟨zb, hb, hzb⟩ := countBound_spec hsat hlogN hr b y hy
    exact ⟨za - zb, by rw [Int.cast_sub, ha, hb]; rfl, (Int.natAbs_sub_le _ _).trans (by omega)⟩
  | .mul a b, k, h => by
    obtain ⟨x, y, hx, hy, rfl⟩ := bind_map_eq_some h
    obtain ⟨za, ha, hza⟩ := countBound_spec hsat hlogN hr a x hx
    obtain ⟨zb, hb, hzb⟩ := countBound_spec hsat hlogN hr b y hy
    exact ⟨za * zb, by rw [Int.cast_mul, ha, hb]; rfl, by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul hza hzb⟩
  | .prepCur _, k, h | .prepNext _, k, h | .periodic _, k, h | .pub _, k, h => by
    simp only [Expr.countBound, reduceCtorEq] at h

/-- The queries of a list of tuples have magnitudes summing to at most their `queryBound`. -/
theorem queryBound_spec {A : Air F} {logN : Nat} {trace : Array F} {pv : List F}
    (hsat : A.Satisfied logN trace pv) (hlogN : logN ≤ twoAdicity F) {r : Nat}
    (hr : r < 2 ^ logN) : ∀ (ts : List (List (Expr F) × Count F)) (k : Nat),
      A.queryBound ts = some k →
      ((ts.filter (0 < ·.2.weight)).map fun t ↦
        (intValue (t.2.expr.eval (generationRow A logN trace pv r))).natAbs).sum ≤ k
  | [], k, _ => Nat.zero_le k
  | t :: ts, k, h => by
    unfold Air.queryBound at h
    rw [List.filter_cons]
    split at h
    · rename_i hw
      obtain ⟨x, y, hx, hy, rfl⟩ := bind_map_eq_some h
      obtain ⟨z, hz, hzx⟩ := countBound_spec hsat hlogN hr _ x hx
      simp only [hw, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
      exact Nat.add_le_add ((natAbs_intValue_le _ z hz).trans hzx)
        (queryBound_spec hsat hlogN hr ts y hy)
    · rename_i hw
      simp only [hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact queryBound_spec hsat hlogN hr ts k h

/-- **The count check is sound.** An AIR passing `countsChecked` bounds its queries'
multiplicities on traces of `2 ^ logN` rows, for a trace domain in the base field. -/
theorem countsBounded_of_countsChecked {A : Air F} (h : A.countsChecked = true) {logN : Nat}
    (hlogN : logN ≤ twoAdicity F) : A.CountsBounded logN := by
  intro trace pv hsat r hr
  rw [List.filter_flatMap, List.map_flatMap, sum_flatMap]
  refine List.sum_le_sum fun l hl ↦ ?_
  have hl := List.all_eq_true.mp h l hl
  obtain ⟨k, hk, hkw⟩ : ∃ k, A.queryBound l.entries = some k ∧ k ≤ l.countWeight := by
    cases hq : A.queryBound l.entries with
    | none => rw [hq] at hl; exact absurd hl Bool.false_ne_true
    | some k =>
      rw [hq] at hl
      exact ⟨k, rfl, of_decide_eq_true hl⟩
  exact (queryBound_spec hsat hlogN hr _ k hk).trans hkw

/-- Every AIR of a batch passing `countsChecked` bounds its queries' multiplicities. -/
theorem _root_.CompStark.Iop.Batch.Setup.countsBounded_of_countsChecked {EF : Type}
    [Challenge F EF] {withLookups : Bool} (S : Iop.Batch.Setup EF withLookups)
    (h : ∀ i, (S.air i).countsChecked = true) (i : Fin S.k) :
    (S.air i).CountsBounded (S.logN i) :=
  Batch.countsBounded_of_countsChecked (h i) (by have := (S.valid i).twoAdic; omega)

/-- Every AIR of a batch statement passing `countsChecked` bounds its queries' multiplicities at
every admitted vector of lengths. -/
theorem _root_.CompStark.Iop.Batch.Statement.countsBounded_of_countsChecked
    (C : Iop.Batch.Statement F) (h : ∀ i, (C.air i).countsChecked = true) (n : Fin C.k → ℕ)
    (hn : C.Admits n) (i : Fin C.k) : (C.air i).CountsBounded (n i) :=
  Batch.countsBounded_of_countsChecked (h i) (by have := (hn.sound i).twoAdic; omega)

end CompStark.Sound.Batch
