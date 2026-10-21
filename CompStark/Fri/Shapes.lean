/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fri.Assumptions
public import CompStark.Stark.Fast.OpeningsSpec

/-! # Shapes through the prover

The sizes of the specification's intermediate values: parallel ranges concatenate to their total
size (`size_parChunks`), a fold halves (`size_foldPairs`), the batched reductions have `2 ^ h`
values for height `2 ^ h` (`reduce_shape`), and the fold schedule folds no further than the
tallest input (`sum_foldSchedule_le`).
-/

@[expose] public section
namespace CompStark.Fri
open CompStark.Stark

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

theorem size_parChunks {α : Type} (n parts : Nat) (f : Nat → Nat → Array α)
    (hf : ∀ s len, (f s len).size = len) (hp : 0 < parts ∨ n = 0) :
    (parChunks n parts f).size = n := by
  unfold parChunks
  generalize hsz : (n + parts - 1) / parts = size
  have hstep : ∀ k, ((List.range k).foldl (fun acc i ↦ acc ++
      f (i * size) (min size (n - min n (i * size)))) #[]).size = min n (k * size) := by
    intro k
    induction k with
    | zero => rw [List.range_zero, List.foldl_nil, Nat.zero_mul, Nat.min_zero]; rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_append,
        ih, hf, Nat.succ_mul]
      omega
  have hn : min n (parts * size) = n := by
    rcases hp with hp | hp
    · have := Nat.lt_div_mul_add (a := n + parts - 1) hp
      rw [hsz] at this
      rw [Nat.min_eq_left (by rw [Nat.mul_comm]; omega)]
    · rw [hp, Nat.zero_min]
  rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range]
  have := hstep parts
  rw [hn] at this
  exact this

theorem size_foldl_push {α β : Type} (g : β → α) :
    ∀ (l : List β) (init : Array α), (l.foldl (fun o k ↦ o.push (g k)) init).size =
      init.size + l.length
  | [], _ => rfl
  | k :: l, init => by
    rw [List.foldl_cons, size_foldl_push g l, Array.size_push, List.length_cons]; omega

theorem size_foldRange (vs : Array EF) (pw : Array F) (perm : Array Nat) (beta half : EF)
    (r0 len : Nat) : (foldRange vs pw perm beta half r0 len).size = len := by
  simp only [foldRange, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  show Array.size (List.foldl _ _ _) = _
  rw [size_foldl_push, Array.emptyWithCapacity_eq, Array.size_empty, List.length_range']
  omega

theorem size_foldPairs (vs : Array EF) (beta : EF) (k : Nat) :
    (foldPairs vs beta k).size = 2 ^ k :=
  size_parChunks _ _ _ (fun _ _ ↦ size_foldRange ..) (by split <;> simp only [Nat.zero_lt_one,
    Nat.ofNat_pos, true_or])

theorem size_accumulateRows (acc comp : Array EF) (xs : Array F) (z yz offset : EF)
    (r0 len : Nat) : (accumulateRows acc comp xs z yz offset r0 len).size = len := by
  simp only [accumulateRows, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  show Array.size (List.foldl _ _ _) = _
  rw [size_foldl_push, Array.emptyWithCapacity_eq, Array.size_empty, List.length_range']
  omega

/-- The largest of a nonempty list of one value, from a smaller start, is that value. -/
theorem foldl_max_const (a : Nat) : ∀ (l : List Nat) (acc : Nat), (∀ x ∈ l, x = a) → l ≠ [] →
    acc ≤ a → l.foldl max acc = a
  | [], _, _, hne, _ => absurd rfl hne
  | [x], acc, h, _, hacc => by
    rw [List.foldl_cons, List.foldl_nil, h x List.mem_cons_self]; exact Nat.max_eq_right hacc
  | x :: y :: l, acc, h, _, hacc => by
    rw [List.foldl_cons, h x List.mem_cons_self, Nat.max_eq_right hacc]
    exact foldl_max_const a (y :: l) a (fun z hz ↦ h z (List.mem_cons_of_mem _ hz))
      (List.cons_ne_nil _ _) le_rfl

/-- Sorting and deduplicating a nonempty list of one value leaves that value. -/
theorem dedup_mergeSort_const (a : Nat) (l : List Nat) (r : Nat → Nat → Bool)
    (h : ∀ x ∈ l, x = a) (hne : l ≠ []) : (l.mergeSort r).dedup = [a] := by
  have hd : ∀ x ∈ (l.mergeSort r).dedup, x = a := fun x hx ↦
    h x (List.mem_mergeSort.mp (List.mem_dedup.mp hx))
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
  have ha : a ∈ (l.mergeSort r).dedup :=
    List.mem_dedup.mpr (List.mem_mergeSort.mpr (h y hy ▸ hy))
  have hrep := List.eq_replicate_iff.mpr ⟨rfl, hd⟩
  have hnd := List.nodup_dedup (l.mergeSort r)
  rw [hrep] at hnd ha ⊢
  have h1 := List.nodup_replicate.mp hnd
  have h0 := List.length_pos_of_mem ha
  try simp only [List.length_replicate] at h0 h1
  rw [show (l.mergeSort r).dedup.length = 1 by omega]
  rfl

/-- With one input, the fold schedule is `foldArities`. -/
theorem foldSchedule_single (m f : Nat) (hm : 0 < m) : ∀ fuel h, h - f ≤ fuel →
    foldSchedule m f fuel [h] = foldArities m (h - f)
  | 0, h, hh => by rw [show h - f = 0 by omega, foldArities]; rfl
  | fuel + 1, h, hh => by
    rw [foldSchedule]
    split
    · rename_i hf
      rw [show h - f = 0 by omega, foldArities]
    · rename_i hf
      obtain ⟨r, hr⟩ : ∃ r, h - f = r + 1 := ⟨h - f - 1, by omega⟩
      rw [hr, foldArities]
      simp only [List.headD_nil, List.head?_nil, reduceCtorEq, ↓reduceIte, List.cons.injEq]
      have hla : min (min (h - f) (r + 1)) m = max 1 (min m (r + 1)) := by omega
      refine ⟨hla, ?_⟩
      rw [hla, foldSchedule_single m f hm fuel _ (by omega)]
      congr 1
      omega

/-- The arities of the fold schedule add up to at most the tallest log height. -/
theorem sum_foldSchedule_le (m f : Nat) : ∀ fuel heights,
    (foldSchedule m f fuel heights).sum ≤ heights.headD 0
  | 0, _ => Nat.zero_le _
  | fuel + 1, [] => Nat.zero_le _
  | fuel + 1, h :: rest => by
    rw [foldSchedule]
    split
    · exact Nat.zero_le _
    · rename_i hf
      dsimp only
      generalize hla : min (min _ (h - f)) m = la
      have hle : la ≤ h - f := by rw [← hla]; omega
      rw [List.sum_cons]
      have hhead : (if rest.head? = some (h - la) then (h - la) :: rest.tail
          else (h - la) :: rest).headD 0 = h - la := by split <;> rfl
      have := sum_foldSchedule_le m f fuel
        (if rest.head? = some (h - la) then (h - la) :: rest.tail else (h - la) :: rest)
      rw [hhead] at this
      rw [List.headD_cons]
      omega

theorem size_flatMap_coeffs (a : Array EF) :
    (a.flatMap fun x ↦ (Ext.coeffs x).toArray).size = Challenge.d EF * a.size := by
  rw [← Array.length_toList, Array.toList_flatMap, List.length_flatMap]
  simp only [Ext.coeffs, Challenge.length_coeffs]
  rw [List.map_const', List.sum_replicate, Array.length_toList, smul_eq_mul, Nat.mul_comm]

/-- Up to `2 ^ 26` words are always addressable. -/
theorem addressable_of_le {n : Nat} (h : n ≤ 2 ^ 26) : Addressable n := by
  have := USize.le_size
  unfold Addressable
  omega

/-- One matrix of the reduction keeps every running sum at `2 ^ h` values for height `2 ^ h`. -/
theorem reduceStep_shape (alpha : EF) (red : List (Nat × Nat × Array EF))
    (hred : ∀ e ∈ red, e.1 ≤ twoAdicity F ∧ e.2.2.size = 2 ^ e.1)
    (it : Mat F × List (EF × Array EF))
    (hit : MatOk it.1) : ∀ e ∈ reduceStep alpha red it,
    e.1 ≤ twoAdicity F ∧ e.2.2.size = 2 ^ e.1 := by
  obtain ⟨-, ⟨k, hk, hh⟩, -⟩ := hit
  have hlog : Nat.log2 it.1.height = k := by rw [hh, Nat.log2_two_pow]
  have hstart : ((red.lookup k).getD (0, Array.replicate it.1.height 0)).2.size = 2 ^ k := by
    cases hl : red.lookup k with
    | none => rw [Option.getD_none, Array.size_replicate, hh]
    | some v =>
      obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hl
      have := (hred (k, v) (by rw [e]; simp only [List.mem_append, List.mem_cons, true_or,
        or_true])).2
      exact this
  have hfold : ∀ (f : Nat × Array EF → EF × Array EF → Nat × Array EF),
      (∀ b p, (f b p).2.size = 2 ^ k) → ∀ (pts : List (EF × Array EF)) (b : Nat × Array EF),
      b.2.size = 2 ^ k → (pts.foldl f b).2.size = 2 ^ k := by
    intro f hf pts
    induction pts with
    | nil => intro b hb; exact hb
    | cons p pts ih => intro b _; rw [List.foldl_cons]; exact ih _ (hf b p)
  intro e he
  simp only [reduceStep, List.mem_cons, List.mem_filter] at he
  rcases he with rfl | ⟨he, -⟩
  · refine ⟨by rw [hlog]; exact hk, ?_⟩
    rw [hlog]
    refine hfold _ (fun b p ↦ ?_) _ _ hstart
    rw [size_parChunks _ _ _ (fun _ _ ↦ size_accumulateRows ..)
      (by split <;> simp only [Nat.zero_lt_one, Nat.ofNat_pos, true_or]), hh]
  · exact hred e he

/-- The batched reductions of matrices of the prover's shapes have `2 ^ h` values. -/
theorem reduce_shape (alpha : EF) (items : List (Mat F × List (EF × Array EF)))
    (hok : ∀ x ∈ items, MatOk x.1) : ∀ y ∈ Fri.reduce alpha items, ∃ s ≤ twoAdicity F,
    y.2.size = 2 ^ s := by
  have hinv : ∀ (l : List (Mat F × List (EF × Array EF))) (red : List (Nat × Nat × Array EF)),
      (∀ x ∈ l, MatOk x.1) → (∀ e ∈ red, e.1 ≤ twoAdicity F ∧ e.2.2.size = 2 ^ e.1) →
      ∀ e ∈ l.foldl (reduceStep alpha) red, e.1 ≤ twoAdicity F ∧ e.2.2.size = 2 ^ e.1 := by
    intro l
    induction l with
    | nil => intro red _ hred; exact hred
    | cons it l ih =>
      intro red hl hred
      rw [List.foldl_cons]
      exact ih _ (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx))
        (reduceStep_shape alpha red hred it (hl it List.mem_cons_self))
  intro y hy
  rw [reduce_eq] at hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
  have := hinv items [] hok (fun _ h ↦ absurd h (List.not_mem_nil)) e (List.mem_mergeSort.mp he)
  exact ⟨e.1, this.1, this.2⟩

theorem size_flatten_ofFn {α : Type} (n w : Nat) (f : Fin n → Array α)
    (hf : ∀ i, (f i).size = w) : (Array.ofFn f).flatten.size = n * w := by
  rw [← Array.length_toList, Array.toList_flatten, List.length_flatten, Array.toList_ofFn,
    List.map_ofFn, List.map_ofFn]
  have : (List.length ∘ Array.toList ∘ f) = fun _ ↦ w := by
    funext i; simp only [Function.comp, Array.length_toList, hf]
  rw [this, List.ofFn_const, List.sum_replicate, smul_eq_mul]

/-- The specification's extension of a `2 ^ logH × w` matrix by `2 ^ bits`. -/
theorem shape_ldeRef (logH bits : Nat) (shift : F) (w : Nat) (m : Array F) :
    (ldeRef logH bits shift w m).width = w ∧ (ldeRef logH bits shift w m).height =
      2 ^ (logH + bits) ∧ (ldeRef logH bits shift w m).values.size = w * 2 ^ (logH + bits) := by
  refine ⟨rfl, rfl, ?_⟩
  show (Array.ofFn _).flatten.size = _
  rw [size_flatten_ofFn _ w _ (fun _ ↦ by
    simp only [Array.size_map, List.size_toArray, List.length_map, List.length_range]),
    Nat.mul_comm]

end CompStark.Fri
