/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.Bus and BusSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Leaves
public import CompStark.Multilinear.Algebra.PaddedProduct

/-! The bus's product test with arbitrary padding rows.

Each pushed or pulled leaf is a polynomial in the challenges `(β, α)`: on an executed row the
factor `β - fp(α, tuple)`, on a padding row the `β`-free `1 - fp(α, row) + fp(α, padding row)`,
which is nonzero because the separators cancel. A side's product is a nonzero `β`-free padding
product times the grand product of its executed encodings (`busPolynomial_factorization`), so an
unbalanced system has different pushed and pulled polynomials, and their roots collide at a
uniform `(α, β)` with probability at most `max 1 k · 2 ^ μ / |E|` (`unbalanced_root_collision_le`).
A nonzero root of the nonzero tree has every nonzero column nonzero on executed rows
(`nonzero_of_root_ne_zero`), whatever the padding. -/

@[expose] public section

namespace CompStark.Tables.System

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear OracleComp

variable (S : System K) (L : Layout S.tables.length) (k : ℕ) (w : Witness K S.tables.length)

/-- The fingerprint polynomial of a base-field tuple evaluates to its fingerprint. -/
theorem fingerprintPoly_eval (α : Fin k → E) (v : Vector K (2 ^ k)) :
    MvPolynomial.eval α (Algebra.fingerprintPoly (v.map ofK)) = fingerprint k α v := by
  have hv : v.map ofK = Vector.ofFn (fun i : Fin (2 ^ k) ↦ ofK v[i]) := by ext i; simp
  rw [hv, fingerprint, fingerprintE]
  simp only [Algebra.fingerprintPoly, map_sum, map_mul, map_prod,
    MvPolynomial.eval_C, MvPolynomial.eval_X, apply_ite, map_sub, map_one,
    Fin.getElem_fin, Vector.getElem_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (ofK v[i] * ·)
  apply Finset.prod_congr rfl
  intro j _
  simp only [eqFactor, bit]
  split <;> simp

/-- The encoding of an interaction's tuple at a row environment. -/
def encodeAt (I : Interaction K) (env : Expr.Env K K) : Vector K (2 ^ k) :=
  encode k (S.busIndex I.bus) (I.tuple.map (Expr.eval env))

/-- The `β`-free leaf of a padding row. -/
noncomputable def paddingPoly (t : Fin S.tables.length) (I : Interaction K) (i : ℕ) :
    MvPolynomial (Fin k) E :=
  1 - Algebra.fingerprintPoly ((S.encodeAt k I (S.env L w t i)).map ofK) +
    Algebra.fingerprintPoly ((S.encodeAt k I (S.paddingEnv L t i)).map ofK)

/-- A padding leaf is a nonzero polynomial: at `α = 0` it is one, the separators cancelling. -/
theorem paddingPoly_ne_zero (t : Fin S.tables.length) (I : Interaction K) (i : ℕ) :
    S.paddingPoly L k w t I i ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin k ↦ (0 : E))) h
  have hv : (Algebra.boolVec (⟨0, Nat.two_pow_pos k⟩ : Fin (2 ^ k)) : Vector E k) =
      Vector.replicate k 0 := by
    ext j; simp [Algebra.boolVec]
  have ev (v : Vector E (2 ^ k)) : MvPolynomial.eval (fun _ : Fin k ↦ (0 : E))
      (Algebra.fingerprintPoly v) = v[0]'(Nat.two_pow_pos k) := by
    have h := Algebra.eval_fingerprintPoly_boolVec (n := k) v ⟨0, Nat.two_pow_pos k⟩
    rw [hv] at h
    simp only [Vector.getElem_replicate, Fin.getElem_fin] at h
    exact h
  have h0 (env : Expr.Env K K) :
      ((S.encodeAt k I env).map ofK)[0]'(Nat.two_pow_pos k) = ofK (gpow (S.busIndex I.bus)) := by
    rw [Vector.getElem_map]
    simp only [encodeAt, encode, Vector.getElem_ofFn, List.getD_cons_zero]
  simp only [paddingPoly, map_add, map_sub, map_one, map_zero] at he
  rw [ev, ev, h0, h0, sub_add_cancel] at he
  exact one_ne_zero he

/-- Each padding leaf has total degree at most `k`. -/
theorem paddingPoly_degree (t : Fin S.tables.length) (I : Interaction K) (i : ℕ) :
    (S.paddingPoly L k w t I i).totalDegree ≤ k :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le
    ((MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) (Algebra.totalDegree_fingerprintPoly _)))
    (Algebra.totalDegree_fingerprintPoly _))

/-- A leaf as a polynomial in `(β, α)`: an executed factor or a `β`-free padding leaf. -/
noncomputable def symbolicLeaf : Block S.tables.length → ℕ → MvPolynomial (Option (Fin k)) E
  | .interaction t I, i =>
    if i < L.executed t then Algebra.fingerprintFactorPoly ((S.encodeAt k I (S.env L w t i)).map ofK)
    else MvPolynomial.rename some (S.paddingPoly L k w t I i)
  | .nonzero _ _, _ => 1

/-- Every symbolic leaf has total degree at most `max 1 k`. -/
theorem symbolicLeaf_degree (b : Block S.tables.length) (i : ℕ) :
    (S.symbolicLeaf L k w b i).totalDegree ≤ max 1 k := by
  match b with
  | .nonzero _ _ => simp only [symbolicLeaf, MvPolynomial.totalDegree_one]; exact Nat.zero_le _
  | .interaction t I =>
    simp only [symbolicLeaf]
    split_ifs
    · exact Algebra.totalDegree_fingerprintFactorPoly _
    · exact (MvPolynomial.totalDegree_rename_le _ _).trans
        ((S.paddingPoly_degree L k w t I i).trans (le_max_right _ _))

/-- A symbolic leaf of an interaction evaluates to the actual leaf. -/
theorem symbolicLeaf_eval (t : Fin S.tables.length) (I : Interaction K) (i : ℕ) (α : Fin k → E) (β : E) :
    MvPolynomial.eval (fun x : Option (Fin k) ↦ x.elim β α) (S.symbolicLeaf L k w (.interaction t I) i) =
      S.blockLeaf L k w α β (.interaction t I) i := by
  have hfp (v : Vector K (2 ^ k)) : MvPolynomial.eval (fun x : Option (Fin k) ↦ x.elim β α)
      (Algebra.fingerprintFactorPoly (v.map ofK)) = β - fingerprint k α v := by
    simp only [Algebra.fingerprintFactorPoly, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename,
      Function.comp_def, Option.elim_some]
    exact congrArg (β - ·) (fingerprintPoly_eval k α v)
  by_cases hi : i < L.executed t
  · simp only [symbolicLeaf, hi, ↓reduceIte, hfp]
    rw [blockLeaf_executed S L k w α β (.interaction t I) i hi]
    rfl
  · simp only [symbolicLeaf, hi, ↓reduceIte]
    simp only [blockLeaf, Block.table, show L.executed t ≤ i by omega, ↓reduceIte, blockForm,
      paddingPoly, MvPolynomial.eval_rename, map_add, map_sub, map_one, Function.comp_def,
      Option.elim_some, fingerprintPoly_eval]
    simp only [encodeAt]
    ring

/-- Every leaf occurrence of a side's blocks. -/
def busEntries (side : Fin 3) : List (Block S.tables.length × ℕ) :=
  (S.blocks side).flatMap fun b ↦ (List.range (2 ^ Block.height S L b)).map (b, ·)

/-- A side's product as a polynomial in `(β, α)`. -/
noncomputable def busPolynomial (side : Fin 3) : MvPolynomial (Option (Fin k)) E :=
  ((S.busEntries L side).map fun p ↦ S.symbolicLeaf L k w p.1 p.2).prod

/-- A side's polynomial has total degree at most `max 1 k · 2 ^ μ` when its blocks fit `2 ^ μ`
leaves. -/
theorem busPolynomial_degree (μ : ℕ) (fits : S.Fits L μ) (side : Fin 3) :
    (S.busPolynomial L k w side).totalDegree ≤ max 1 k * 2 ^ μ := by
  have bound (xs : List (Block S.tables.length × ℕ)) :
      ((xs.map fun p ↦ S.symbolicLeaf L k w p.1 p.2).prod).totalDegree ≤ max 1 k * xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      exact (MvPolynomial.totalDegree_mul _ _).trans
        ((Nat.add_le_add (S.symbolicLeaf_degree L k w _ _) ih).trans (by rw [Nat.mul_succ]; omega))
  have hlen : (S.busEntries L side).length = ((S.blocks side).map fun b ↦ 2 ^ Block.height S L b).sum := by
    simp only [busEntries, List.length_flatMap, List.length_map, List.length_range]
  exact (bound _).trans (Nat.mul_le_mul_left _ (hlen ▸ fits side))

/-- The leaves of a side multiply to the product of its blocks' leaves, whatever the padding. -/
theorem root_eq_allBlocks (μ : ℕ) (fits : S.Fits L μ) (α : Fin k → E) (β : E) (side : Fin 3) :
    GrandProduct.level μ 0 (S.leaves L k w α β) side 0 =
      ((S.blocks side).map fun b ↦ ∏ i ∈ Finset.range (2 ^ Block.height S L b),
        S.blockLeaf L k w α β b i).prod := by
  have perm := List.mergeSort_perm (S.blocks side)
    (fun a b ↦ decide (Block.height S L b ≤ Block.height S L a))
  have fitSorted : ((S.sortedBlocks L side).map fun b ↦ 2 ^ Block.height S L b).sum ≤ 2 ^ μ :=
    (perm.map fun b ↦ 2 ^ Block.height S L b).sum_eq ▸ fits side
  simp only [GrandProduct.level, Nat.sub_zero, Nat.zero_mul, Nat.zero_add, leaves]
  rw [Fin.prod_univ_eq_prod_range (fun j ↦ S.stackLeaves L k w α β (S.sortedBlocks L side) j),
    prod_stackLeaves S L k w α β _ _ fitSorted]
  exact (perm.map _).prod_eq

/-- The pushed or pulled polynomial evaluates to its tree's root. -/
theorem busPolynomial_eval (μ : ℕ) (fits : S.Fits L μ) (side : Fin 3) (hside : side.val ≠ 2)
    (α : Fin k → E) (β : E) :
    MvPolynomial.eval (fun x : Option (Fin k) ↦ x.elim β α) (S.busPolynomial L k w side) =
      GrandProduct.level μ 0 (S.leaves L k w α β) side 0 := by
  rw [root_eq_allBlocks S L k w μ fits α β side, busPolynomial, map_list_prod, busEntries,
    List.map_flatMap, List.map_flatMap, prod_flatMap]
  apply congrArg List.prod
  apply List.map_congr_left
  intro b hb
  rw [prod_range_list]
  apply congrArg List.prod
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro i _
  cases b with
  | interaction t I => exact S.symbolicLeaf_eval L k w t I i α β
  | nonzero t c =>
    exfalso
    simp only [blocks, hside, ↓reduceIte, List.mem_flatMap, List.mem_finRange, true_and,
      List.mem_map] at hb
    obtain ⟨_, _, _, h⟩ := hb
    cases h

/-- Whether a leaf occurrence is an executed row. -/
def executedEntry (p : Block S.tables.length × ℕ) : Bool := decide (p.2 < L.executed (Block.table S p.1))

/-- The `β`-free leaf of an occurrence, one on executed rows. -/
noncomputable def paddingAt : Block S.tables.length × ℕ → MvPolynomial (Fin k) E
  | (.interaction t I, i) => S.paddingPoly L k w t I i
  | (.nonzero _ _, _) => 1

/-- The `β`-free product of a list of occurrences' padding leaves. -/
noncomputable def paddingProduct (xs : List (Block S.tables.length × ℕ)) : MvPolynomial (Fin k) E :=
  (xs.map fun p ↦ if S.executedEntry L p then 1 else S.paddingAt L k w p).prod

/-- A padding product is not the zero polynomial. -/
theorem paddingProduct_ne_zero (xs : List (Block S.tables.length × ℕ)) :
    S.paddingProduct L k w xs ≠ 0 := by
  induction xs with
  | nil => exact one_ne_zero
  | cons x xs ih =>
    change (if S.executedEntry L x then 1 else S.paddingAt L k w x) * S.paddingProduct L k w xs ≠ 0
    apply mul_ne_zero _ ih
    split
    · exact one_ne_zero
    · obtain ⟨b, i⟩ := x
      cases b with
      | interaction t I => exact S.paddingPoly_ne_zero L k w t I i
      | nonzero => exact one_ne_zero

/-- The encoding of an executed interaction occurrence. -/
def entryEncoding (p : Block S.tables.length × ℕ) : Vector K (2 ^ k) :=
  match p with
  | (.interaction t I, i) => S.encodeAt k I (S.env L w t i)
  | (.nonzero _ _, _) => encode k 0 []

/-- A list of interaction occurrences factors into its padding and its executed encodings'
grand product. -/
theorem symbolicProduct_factorization (xs : List (Block S.tables.length × ℕ))
    (hxs : ∀ p ∈ xs, ∃ t I, p.1 = .interaction t I) :
    (xs.map fun p ↦ S.symbolicLeaf L k w p.1 p.2).prod =
      MvPolynomial.rename some (S.paddingProduct L k w xs) *
      Algebra.grandProductPoly (((xs.filter (S.executedEntry L)).map
        fun p ↦ (S.entryEncoding L k w p).map ofK : List _) : Multiset _) := by
  simp only [paddingProduct, Algebra.grandProductPoly, Multiset.map_coe, Multiset.prod_coe,
    List.map_map, Function.comp_def]
  induction xs with
  | nil => simp only [List.map_nil, List.prod_nil, List.filter_nil, map_one, mul_one]
  | cons x xs ih =>
    obtain ⟨t, I, hx⟩ := hxs x (List.mem_cons_self ..)
    obtain ⟨b, i⟩ := x
    simp only at hx
    subst hx
    have rest := ih fun p hp ↦ hxs p (List.mem_cons_of_mem _ hp)
    by_cases he : i < L.executed t
    · have hb : S.executedEntry L (.interaction t I, i) = true := by
        simp only [executedEntry, Block.table, he, decide_true]
      have hl : S.symbolicLeaf L k w (.interaction t I) i =
          Algebra.fingerprintFactorPoly ((S.encodeAt k I (S.env L w t i)).map ofK) := by
        simp only [symbolicLeaf, he, ↓reduceIte]
      rw [List.map_cons, List.prod_cons, rest, hl]
      simp only [List.map_cons, List.prod_cons, List.filter_cons, hb, ↓reduceIte, one_mul, entryEncoding]
      exact mul_left_comm _ _ _
    · have hb : S.executedEntry L (.interaction t I, i) = false := by
        simp only [executedEntry, Block.table, he, decide_false]
      have hl : S.symbolicLeaf L k w (.interaction t I) i =
          MvPolynomial.rename some (S.paddingPoly L k w t I i) := by
        simp only [symbolicLeaf, he, ↓reduceIte]
      rw [List.map_cons, List.prod_cons, rest, hl]
      simp only [List.map_cons, List.prod_cons, List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte,
        paddingAt, map_mul, mul_assoc]

/-- A list transposes under a double `flatMap` up to permutation. -/
theorem flatMap_map_transpose {A B C : Type} (xs : List A) (ys : List B) (f : A → B → C) :
    (xs.flatMap fun x ↦ ys.map (f x)).Perm (ys.flatMap fun y ↦ xs.map (fun x ↦ f x y)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (List.Perm.append (List.Perm.refl _) ih).trans (List.map_append_flatMap_perm _ _ _)

/-- Filtering a larger initial interval by a smaller endpoint gives that interval. -/
theorem filter_range_lt (n m : ℕ) (hm : m ≤ n) :
    (List.range n).filter (fun i ↦ decide (i < m)) = List.range m := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    by_cases h : m ≤ n
    · simp only [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil,
        show ¬ n < m by omega, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil, ih h]
    · have : m = n + 1 := by omega
      subst m
      exact List.filter_eq_self.mpr (fun i hi ↦ by simpa using List.mem_range.mp hi)

/-- The executed encodings of a side are the encoded pushes or pulls. -/
theorem executed_encodings {width : String → ℕ} (h : S.BusShape k width)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t) (push : Bool) (side : Fin 3)
    (hside : side.val = if push then 0 else 1) :
    (((S.busEntries L side).filter (S.executedEntry L)).map (S.entryEncoding L k w) :
      Multiset (Vector K (2 ^ k))) = S.encoded k L w push := by
  have h2 : side.val ≠ 2 := by split at hside <;> omega
  have hdir : decide (side.val = 0) = push := by cases push <;> simp only [hside, ↓reduceIte] <;> decide
  rw [encoded_eq_emitted S h]
  have hb : S.blocks side = (List.finRange S.tables.length).flatMap fun t ↦
      ((S.table t).interactions.filter (·.push == push)).map (.interaction t) := by
    simp only [blocks, h2, ↓reduceIte, hdir]
  unfold busEntries emitted
  rw [hb, Multiset.map_coe, Multiset.coe_eq_coe, List.flatMap_assoc, List.filter_flatMap,
    List.map_flatMap, List.map_flatMap]
  apply List.Perm.flatMap_left
  intro t _
  rw [List.flatMap_map, List.filter_flatMap, List.map_flatMap, List.map_flatMap]
  have range (I : Interaction K) :
      ((List.range (2 ^ Block.height S L (.interaction t I))).map
          ((Block.interaction t I : Block S.tables.length), ·)).filter (S.executedEntry L) =
        (List.range (L.executed t)).map ((Block.interaction t I : Block S.tables.length), ·) := by
    rw [List.filter_map]
    congr 1
    change List.filter (fun i ↦ decide (i < L.executed t)) (List.range (2 ^ L.logHeight t)) = _
    exact filter_range_lt _ _ (hexec t)
  have rows (I : Interaction K) :
      (((List.range (2 ^ Block.height S L (.interaction t I))).map
          ((Block.interaction t I : Block S.tables.length), ·)).filter (S.executedEntry L)).map
          (S.entryEncoding L k w) =
        (List.range (L.executed t)).map fun i ↦
          encode k (S.busIndex I.bus) (S.emittedTuple L w (t, i, I)) := by
    rw [range, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, entryEncoding, encodeAt, emittedTuple]
  have lhs : ((S.table t).interactions.filter (·.push == push)).flatMap (fun I ↦
      (((List.range (2 ^ Block.height S L (.interaction t I))).map
          ((Block.interaction t I : Block S.tables.length), ·)).filter (S.executedEntry L)).map
          (S.entryEncoding L k w)) =
      ((S.table t).interactions.filter (·.push == push)).flatMap (fun I ↦
        (List.range (L.executed t)).map fun i ↦
          encode k (S.busIndex I.bus) (S.emittedTuple L w (t, i, I))) := by
    congr 1
    funext I
    exact rows I
  refine (List.Perm.of_eq lhs).trans ((flatMap_map_transpose
    ((S.table t).interactions.filter (·.push == push)) (List.range (L.executed t))
    fun I i ↦ encode k (S.busIndex I.bus) (S.emittedTuple L w (t, i, I))).trans (List.Perm.of_eq ?_))
  apply congrArg (List.flatMap · (List.range (L.executed t)))
  funext i
  rw [List.map_map]
  rfl

/-- The pushed or pulled polynomial is its padding times the grand product of the encoded
multiset. -/
theorem busPolynomial_factorization {width : String → ℕ} (h : S.BusShape k width)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t) (push : Bool) (side : Fin 3)
    (hside : side.val = if push then 0 else 1) :
    S.busPolynomial L k w side =
      MvPolynomial.rename some (S.paddingProduct L k w (S.busEntries L side)) *
        Algebra.grandProductPoly ((S.encoded k L w push).map (·.map ofK)) := by
  have h2 : side.val ≠ 2 := by split at hside <;> omega
  have interactions : ∀ p ∈ S.busEntries L side, ∃ t I, p.1 = .interaction t I := by
    intro p hp
    simp only [busEntries, blocks, h2, ↓reduceIte, List.mem_flatMap, List.mem_finRange, true_and,
      List.mem_map] at hp
    obtain ⟨_, ⟨t, I, _, rfl⟩, i, _, rfl⟩ := hp
    exact ⟨t, I, rfl⟩
  rw [busPolynomial, symbolicProduct_factorization S L k w _ interactions,
    ← executed_encodings S L k w h hexec push side hside, Multiset.map_coe, List.map_map]
  rfl

/-- An unbalanced system has different pushed and pulled polynomials. -/
theorem busPolynomial_ne {width : String → ℕ} (h : S.BusShape k width)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t)
    (unbalanced : ¬ ∀ b ∈ S.buses, S.tuples L w b true = S.tuples L w b false) :
    S.busPolynomial L k w 0 ≠ S.busPolynomial L k w 1 := by
  intro heq
  rw [busPolynomial_factorization S L k w h hexec true 0 rfl,
    busPolynomial_factorization S L k w h hexec false 1 rfl] at heq
  have hr := Algebra.paddedGrandProduct_injective _ _ (S.paddingProduct_ne_zero L k w _)
    (S.paddingProduct_ne_zero L k w _) _ _ heq
  have hinj : Function.Injective (fun v : Vector K (2 ^ k) ↦ v.map ofK) := fun v v' hv ↦
    (Vector.map_inj_right fun _ _ h ↦ (algebraMap K E).injective h).mp hv
  exact unbalanced ((S.balanced_iff h L w).mpr (Multiset.map_injective hinj hr))

/-- An unbalanced system's pushed and pulled roots, with arbitrary padding rows, agree at a
uniform `(α, β)` with probability at most `max 1 k · 2 ^ μ / |E|`. -/
theorem unbalanced_root_collision_le {width : String → ℕ} (h : S.BusShape k width)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t) (μ : ℕ) (fits : S.Fits L μ)
    (unbalanced : ¬ ∀ b ∈ S.buses, S.tuples L w b true = S.tuples L w b false) :
    Pr{let ab ← ($ᵗ ((Fin k → E) × E))}[
      GrandProduct.level μ 0 (S.leaves L k w ab.1 ab.2) 0 0 =
        GrandProduct.level μ 0 (S.leaves L k w ab.1 ab.2) 1 0] ≤ overE (max 1 k * 2 ^ μ) := by
  classical
  let P := S.busPolynomial L k w 0
  let Q := S.busPolynomial L k w 1
  have hpq : P - Q ≠ 0 := sub_ne_zero.mpr (S.busPolynomial_ne L k w h hexec unbalanced)
  have hd : (P - Q).totalDegree ≤ max 1 k * 2 ^ μ :=
    (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (S.busPolynomial_degree L k w μ fits 0) (S.busPolynomial_degree L k w μ fits 1))
  let e : (Fin k → E) × E ≃ (Option (Fin k) → E) := {
    toFun := fun ab i ↦ i.elim ab.2 ab.1
    invFun := fun x ↦ (fun i ↦ x (some i), x none)
    left_inv := fun _ ↦ rfl
    right_inv := fun x ↦ funext fun i ↦ by cases i <;> rfl }
  have hcount : Nat.card {ab : (Fin k → E) × E //
      GrandProduct.level μ 0 (S.leaves L k w ab.1 ab.2) 0 0 =
        GrandProduct.level μ 0 (S.leaves L k w ab.1 ab.2) 1 0} ≤
      max 1 k * 2 ^ μ * Fintype.card E ^ k := by
    have hc := MvPolynomial.card_zeros_le_of_totalDegree_le (P - Q) hpq hd
    rw [Nat.card_congr (e.subtypeEquiv (q := fun x ↦ MvPolynomial.eval x (P - Q) = 0) fun ab ↦ by
      rw [MvPolynomial.eval_sub, sub_eq_zero]
      exact (congrArg₂ Eq (S.busPolynomial_eval L k w μ fits 0 (by decide) ab.1 ab.2)
        (S.busPolynomial_eval L k w μ fits 1 (by decide) ab.1 ab.2)).to_iff.symm),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_sub_cancel] using hc
  have hcard : Fintype.card ((Fin k → E) × E) = Fintype.card E * Fintype.card E ^ k := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, mul_comm]
  have hdiv : overE (max 1 k * 2 ^ μ) =
      ((max 1 k * 2 ^ μ * Fintype.card E ^ k : ℕ) : ENNReal) / Fintype.card ((Fin k → E) × E) := by
    rw [overE, hcard, Nat.cast_mul (max 1 k * 2 ^ μ), Nat.cast_mul (Fintype.card E),
      ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero))
        (ENNReal.natCast_ne_top _)]
  rw [hdiv, SampleableType.prEvent_uniformSample_le_div_iff, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  exact hcount

/-- A nonzero root of the nonzero tree has every nonzero column nonzero on executed rows,
whatever the padding. -/
theorem nonzero_of_root_ne_zero (μ : ℕ) (fits : S.Fits L μ)
    (hexec : ∀ t, L.executed t ≤ 2 ^ L.logHeight t) (α : Fin k → E) (β : E)
    (root : GrandProduct.level μ 0 (S.leaves L k w α β) 2 0 ≠ 0) :
    ∀ t, ∀ i < L.executed t, ∀ c ∈ (S.table t).nonzero, ((w t).getD i #[]).getD c 0 ≠ 0 := by
  intro t i hi c hc hz
  apply root
  rw [root_eq_allBlocks S L k w μ fits α β 2, List.prod_eq_zero_iff, List.mem_map]
  refine ⟨.nonzero t c, ?_, ?_⟩
  · simp only [blocks, show (2 : Fin 3).val = 2 from rfl, ↓reduceIte, List.mem_flatMap,
      List.mem_finRange, true_and, List.mem_map]
    exact ⟨t, c, hc, rfl⟩
  · have hh : i < 2 ^ Block.height S L (.nonzero t c) := lt_of_lt_of_le hi (hexec t)
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hh)]
    rw [blockLeaf_executed S L k w α β (.nonzero t c) i hi]
    simp only [blockForm, Block.table, hz]
    exact map_zero (algebraMap K E)

end CompStark.Tables.System
