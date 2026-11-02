/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.HashChain
public import ArkLib.Interaction.Oracle.Security.BcsSimulation
public import CompStark.Merkle.ExtractMixed
public import CompStark.Merkle.Multi

/-! # Merkle commitments on the log of the real oracles

The real game runs the verifier's oracles, the duplex chain and the Merkle hashes (`sumSpec`),
lazily with a log (ArkLib's `Bcs.realImpl`): every entry of the log is the first query of its key.
The message behind a Merkle cap is extracted from the hash answers logged before the duplex query
that absorbs the cap (`Bcs.snapshotAt`). This file bounds the digest clashes that would make that
extraction unstable or not binding, and proves stability and binding without them:

* `boundDigests offs capLen x`: the digests a duplex input `x` can commit to, `capLen` digests
  read from each offset of `offs` (a cap of up to `capLen` digests absorbed at that offset).
* `logDigests pre`: the digests known after the log `pre`: the initial capacity (the zero digest),
  every answered digest (hash or duplex capacity), the children of every compression, and the
  bound digests of every duplex input. `HashBad L`: a hash entry of `L` answers a digest known
  before it.
* `prEvent_hashBad_le`: a program making at most `q` oracle queries logs a `HashBad` log with
  probability at most `hashBadError F capLen offs.length q = (2 + |offs| capLen) q² / |F|⁸`.
* `extractRow_snapshotAt` (and `extractGroup_`, `extractCapRow_`, `matColumnCap_snapshotAt`):
  without `HashBad`, extraction under a digest bound by a logged duplex input from the snapshot
  at that input is extraction from all the logged hash answers (`merkleCache`, `hashCacheOf`).
* `hashCache_injective`, `extractRow_of_logVerifyBatch` (and the mixed-height, multi-opening and
  capped variants): without `HashBad`, an opening accepted on the logged answers (`logHash`,
  `logCompress`, every other hash query answered by a digest `dstar` outside `logDigests`) opens
  the rows extracted from the logged hash answers.
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.RandomOracle OracleSpec OracleComp
open Interaction.Oracle.Security
open scoped ENNReal

/-! ### First entries of a log -/

section Log
variable {κ : Type} [DecidableEq κ] {spec : OracleSpec κ}

theorem cacheOf_eq_none_iff {log : QueryLog spec} {t : κ} :
    Bcs.cacheOf log t = none ↔ t ∉ log.map Sigma.fst := by
  induction log with
  | nil => simp only [Bcs.cacheOf_nil, QueryCache.empty_apply, List.map_nil, List.not_mem_nil,
      not_false_eq_true]
  | cons e log ih =>
    rw [Bcs.cacheOf_cons_eq_none, ih, List.map_cons, List.mem_cons, not_or, ne_comm]

/-- A cached key's answer is the answer of its first entry. -/
theorem exists_first_of_cacheOf {log : QueryLog spec} {t : κ} {u : spec.Range t}
    (h : Bcs.cacheOf log t = some u) :
    ∃ pre post, log = pre ++ ⟨t, u⟩ :: post ∧ t ∉ pre.map Sigma.fst := by
  induction log with
  | nil => simp only [Bcs.cacheOf_nil, QueryCache.empty_apply, reduceCtorEq] at h
  | cons e log ih =>
    obtain ⟨t', u'⟩ := e
    by_cases ht : t = t'
    · subst ht
      rw [Bcs.cacheOf_cons, QueryCache.cacheQuery_self] at h
      obtain rfl := Option.some.inj h
      exact ⟨[], log, rfl, List.not_mem_nil⟩
    · rw [Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ ht] at h
      obtain ⟨pre, post, rfl, hpre⟩ := ih h
      refine ⟨⟨t', u'⟩ :: pre, post, rfl, ?_⟩
      rw [List.map_cons, List.mem_cons, not_or]
      exact ⟨ht, hpre⟩

/-- The first entry of a key gives its cached answer. -/
theorem cacheOf_append_cons {pre post : QueryLog spec} {t : κ} (u : spec.Range t)
    (h : t ∉ pre.map Sigma.fst) : Bcs.cacheOf (pre ++ ⟨t, u⟩ :: post) t = some u := by
  induction pre with
  | nil => rw [List.nil_append, Bcs.cacheOf_cons, QueryCache.cacheQuery_self]
  | cons e pre ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [List.cons_append, Bcs.cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ h.1]
    exact ih h.2

/-- A cached answer stays cached when the log grows. -/
theorem cacheOf_append_of_eq_some {l₁ : QueryLog spec} {t : κ} {u : spec.Range t}
    (h : Bcs.cacheOf l₁ t = some u) (l₂ : QueryLog spec) : Bcs.cacheOf (l₁ ++ l₂) t = some u := by
  obtain ⟨pre, post, rfl, hpre⟩ := exists_first_of_cacheOf h
  rw [List.append_assoc, List.cons_append]
  exact cacheOf_append_cons u hpre

/-- A cached answer is logged. -/
theorem mem_of_cacheOf {log : QueryLog spec} {t : κ} {u : spec.Range t}
    (h : Bcs.cacheOf log t = some u) : (⟨t, u⟩ : (t : κ) × spec.Range t) ∈ log := by
  obtain ⟨pre, post, rfl, -⟩ := exists_first_of_cacheOf h
  exact List.mem_append_right _ List.mem_cons_self

end Log

section Split
variable {β : Type}

/-- Of two splits of one list, the one splitting earlier has its middle element in the other's
front part. -/
theorem exists_mid_of_length_lt {pre₁ post₁ pre₂ post₂ : List β} {e₁ e₂ : β}
    (h : pre₁ ++ e₁ :: post₁ = pre₂ ++ e₂ :: post₂) (hlt : pre₁.length < pre₂.length) :
    ∃ mid, pre₂ = pre₁ ++ e₁ :: mid := by
  rcases List.append_eq_append_iff.mp h with ⟨a', h₂, h₁⟩ | ⟨c', h₁, -⟩
  · rcases a' with _ | ⟨b, mid⟩
    · rw [List.append_nil] at h₂
      rw [h₂] at hlt
      exact absurd hlt (lt_irrefl _)
    · rw [List.cons_append, List.cons.injEq] at h₁
      exact ⟨mid, by rw [h₂, h₁.1]⟩
  · rw [h₁, List.length_append] at hlt
    omega

/-- Two splits of one list at the same position have the same middle element. -/
theorem eq_of_length_eq {pre₁ post₁ pre₂ post₂ : List β} {e₁ e₂ : β}
    (h : pre₁ ++ e₁ :: post₁ = pre₂ ++ e₂ :: post₂) (heq : pre₁.length = pre₂.length) :
    e₁ = e₂ :=
  (List.cons.inj (List.append_inj h heq).2).1

end Split

variable {F : Type} {K : ℕ}

/-! ### Bound digests and clashes -/

/-- `|Digest| = |F| ^ 8`. -/
theorem natCard_digest : Nat.card (Digest F) = Nat.card F ^ 8 := by
  rw [Nat.card_congr (arrayVectorEquivFin F 8), Nat.card_fun, Nat.card_fin]

section Digests
variable [Zero F]

/-- The digest read from `x` at the element offset `o`: the elements `o, …, o + 7`, zero past the
end of `x`. -/
def digestAt (x : List F) (o : ℕ) : Digest F := Vector.ofFn fun j : Fin 8 ↦ x.getD (o + j) 0

/-- The digests a duplex input `x` can commit to: `capLen` consecutive digests read from each
offset of `offs`. -/
def boundDigests (offs : List ℕ) (capLen : ℕ) (x : List F) : List (Digest F) :=
  offs.flatMap fun o ↦ (List.range capLen).map fun j ↦ digestAt x (o + 8 * j)

theorem length_boundDigests (offs : List ℕ) (capLen : ℕ) (x : List F) :
    (boundDigests offs capLen x).length = offs.length * capLen := by
  induction offs with
  | nil => simp only [boundDigests, List.flatMap_nil, List.length_nil, zero_mul]
  | cons o offs ih =>
    simp only [boundDigests, List.flatMap_cons, List.length_append, List.length_map,
      List.length_range, List.length_cons] at ih ⊢
    rw [ih, Nat.succ_mul, Nat.add_comm]

omit [Zero F] in
/-- Entry `i` of digest `j` of a list of digests, flattened. -/
theorem getElem?_flatMap_digests (cap : List (Digest F)) (j i : ℕ) (hj : j < cap.length)
    (hi : i < 8) : (cap.flatMap Vector.toList)[8 * j + i]? = some cap[j][i] := by
  induction cap generalizing j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons c cs ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add,
        List.getElem?_append_left (by rw [Vector.length_toList]; exact hi),
        List.getElem?_eq_getElem (by rw [Vector.length_toList]; exact hi), Vector.getElem_toList]
      rfl
    | succ j =>
      rw [List.getElem?_append_right (by rw [Vector.length_toList]; omega), Vector.length_toList,
        show 8 * (j + 1) + i - 8 = 8 * j + i by omega]
      exact ih j (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hj)

/-- The digest read where entry `j` of a cap was absorbed is that entry. -/
theorem digestAt_cap (pre post : List F) (cap : List (Digest F)) (j : ℕ) (hj : j < cap.length) :
    digestAt (pre ++ cap.flatMap Vector.toList ++ post) (pre.length + 8 * j) = cap[j] := by
  refine Vector.ext fun i hi ↦ ?_
  simp only [digestAt, Vector.getElem_ofFn, List.getD_eq_getElem?_getD]
  rw [List.append_assoc, Nat.add_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left (by rw [length_flatMap_digests]; omega),
    getElem?_flatMap_digests cap j i hj hi]
  rfl

/-- A duplex input binds the digests of a cap of at most `capLen` entries absorbed at an offset
of `offs`. -/
theorem mem_boundDigests_of_cap {offs : List ℕ} {capLen : ℕ} (pre post : List F)
    (cap : List (Digest F)) (hoff : pre.length ∈ offs) (hlen : cap.length ≤ capLen) {d : Digest F}
    (hd : d ∈ cap) : d ∈ boundDigests offs capLen (pre ++ cap.flatMap Vector.toList ++ post) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  exact List.mem_flatMap.mpr ⟨_, hoff, List.mem_map.mpr
    ⟨j, List.mem_range.mpr (by omega), digestAt_cap pre post cap j hj⟩⟩

variable (offs : List ℕ) (capLen : ℕ)

/-- The digests of a log entry: a duplex call's answered capacity and its input's bound digests, a
leaf hash's answer, and a compression's answer and children. -/
def entryDigests : (e : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t) → List (Digest F)
  | ⟨.inl (_, x), a⟩ => a.1 :: boundDigests offs capLen x
  | ⟨.inr (.inl _), u⟩ => [u]
  | ⟨.inr (.inr (left, right)), u⟩ => [u, left, right]

/-- The digests known after the log `pre`: the initial capacity and the digests of its entries. -/
def logDigests (pre : QueryLog (sumSpec F K)) : List (Digest F) :=
  initCap :: pre.flatMap (entryDigests offs capLen)

/-- Some hash entry of `L`, the first of its key, answers a digest known before it. -/
def HashBad (L : QueryLog (sumSpec F K)) : Prop :=
  ∃ (pre : QueryLog (sumSpec F K)) (t : List F ⊕ (Digest F × Digest F)) (u : Digest F)
    (post : QueryLog (sumSpec F K)),
    L = pre ++ ⟨.inr t, u⟩ :: post ∧ Sum.inr t ∉ pre.map Sigma.fst ∧
      u ∈ logDigests offs capLen pre

variable {offs capLen}

theorem mem_logDigests_of_mem {pre : QueryLog (sumSpec F K)}
    {e : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t} (he : e ∈ pre) {d : Digest F}
    (hd : d ∈ entryDigests offs capLen e) : d ∈ logDigests offs capLen pre :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨e, he, hd⟩)

theorem initCap_mem_logDigests (pre : QueryLog (sumSpec F K)) :
    initCap ∈ logDigests offs capLen pre := List.mem_cons_self

theorem answer_mem_entryDigests (t : List F ⊕ (Digest F × Digest F)) (u : Digest F) :
    u ∈ entryDigests (K := K) offs capLen ⟨.inr t, u⟩ := by
  rcases t with row | ⟨left, right⟩ <;> exact List.mem_cons_self

theorem not_hashBad_nil : ¬ HashBad offs capLen ([] : QueryLog (sumSpec F K)) := by
  rintro ⟨pre, t, u, post, h, -⟩
  exact List.append_ne_nil_of_right_ne_nil pre (List.cons_ne_nil _ _) h.symm

/-- Without `HashBad`, the first entry of a hash key answers a digest not known before it. -/
theorem not_mem_logDigests {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    {pre post : QueryLog (sumSpec F K)} {t : List F ⊕ (Digest F × Digest F)} {u : Digest F}
    (h : L = pre ++ ⟨.inr t, u⟩ :: post) (hfresh : Sum.inr t ∉ pre.map Sigma.fst) :
    u ∉ logDigests offs capLen pre :=
  fun hu ↦ hL ⟨pre, t, u, post, h, hfresh, hu⟩

theorem length_entryDigests_le (hB : 0 < offs.length * capLen)
    (e : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t) :
    (entryDigests offs capLen e).length ≤ 2 + offs.length * capLen := by
  rcases e with ⟨⟨s, x⟩ | row | ⟨left, right⟩, u⟩
  · simp only [entryDigests, List.length_cons, length_boundDigests]
    omega
  · simp only [entryDigests, List.length_cons, List.length_nil]
    omega
  · simp only [entryDigests, List.length_cons, List.length_nil]
    omega

theorem length_logDigests_le (hB : 0 < offs.length * capLen)
    (pre : QueryLog (sumSpec F K)) :
    (logDigests offs capLen pre).length ≤ 1 + (2 + offs.length * capLen) * pre.length := by
  induction pre with
  | nil =>
    simp only [logDigests, List.flatMap_nil, List.length_cons, List.length_nil, mul_zero]
    omega
  | cons e pre ih =>
    simp only [logDigests, List.flatMap_cons, List.length_cons, List.length_append] at ih ⊢
    have := length_entryDigests_le hB e
    rw [Nat.mul_succ]
    omega

end Digests

/-! ### The logged hash answers as a Merkle cache -/

/-- Hash answers as a Merkle cache: the leaf hash of `row` answered `y`, and the compression of
`left, right` answered `y`. -/
def merkleCache (c : (merkleSpec F).QueryCache) : Merkle.Cache F (Digest F) where
  leaf row y := c (.inl row) = some y
  node left right y := c (.inr (left, right)) = some y

section Cache
variable [BaseField F] {offs : List ℕ} {capLen : ℕ}

theorem hashCacheOf_apply (L : QueryLog (sumSpec F K)) (t : List F ⊕ (Digest F × Digest F)) :
    Bcs.hashCacheOf L t = Bcs.cacheOf L (.inr t) := rfl

/-- Without `HashBad`, distinct logged hash keys have distinct answers. -/
theorem hashKey_eq_of_answer_eq {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    {t t' : List F ⊕ (Digest F × Digest F)} {y : Digest F}
    (h : Bcs.cacheOf L (.inr t) = some y) (h' : Bcs.cacheOf L (.inr t') = some y) : t = t' := by
  obtain ⟨pre, post, hL₁, hfresh⟩ := exists_first_of_cacheOf h
  obtain ⟨pre', post', hL₂, hfresh'⟩ := exists_first_of_cacheOf h'
  have hsplit := hL₁.symm.trans hL₂
  rcases lt_trichotomy pre.length pre'.length with hlt | heq | hgt
  · obtain ⟨mid, hmid⟩ := exists_mid_of_length_lt hsplit hlt
    refine absurd (mem_logDigests_of_mem (hmid ▸ List.mem_append_right _ List.mem_cons_self)
      (answer_mem_entryDigests t y)) (not_mem_logDigests hL hL₂ hfresh')
  · have := congrArg Sigma.fst (eq_of_length_eq hsplit heq)
    exact Sum.inr.inj this
  · obtain ⟨mid, hmid⟩ := exists_mid_of_length_lt hsplit.symm hgt
    refine absurd (mem_logDigests_of_mem (hmid ▸ List.mem_append_right _ List.mem_cons_self)
      (answer_mem_entryDigests t' y)) (not_mem_logDigests hL hL₁ hfresh)

/-- **No collision.** Without `HashBad`, no two logged hash queries share an answer. -/
theorem hashCache_injective {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L) :
    (merkleCache (Bcs.hashCacheOf L)).Injective where
  leaf _ _ _ h h' := Sum.inl.inj (hashKey_eq_of_answer_eq hL h h')
  node _ _ _ _ _ h h' :=
    Prod.mk.inj (Sum.inr.inj (hashKey_eq_of_answer_eq hL h h'))

end Cache

/-! ### Stability of extraction -/

section Stable
variable [BaseField F] {offs : List ℕ} {capLen : ℕ}

/-- The snapshot at a chain key is the hash answers before its first entry. -/
theorem snapshotAt_eq {pre post : QueryLog (sumSpec F K)} {q : Digest F × List F}
    (a : Digest F × Vector F K) (hfresh : Sum.inl q ∉ pre.map Sigma.fst) :
    Bcs.snapshotAt (pre ++ ⟨.inl q, a⟩ :: post) q = Bcs.hashCacheOf pre := by
  unfold Bcs.snapshotAt
  rw [List.takeWhile_append_of_pos fun e he ↦ ?_]
  · simp only [ne_eq, not_true_eq_false, decide_false, List.takeWhile_cons_of_neg,
      Bool.false_eq_true, not_false_eq_true, List.append_nil]
  · simp only [ne_eq, decide_eq_true_eq]
    intro h
    exact hfresh (h ▸ List.mem_map_of_mem (f := Sigma.fst) he)

/-- **No prediction.** Without `HashBad`, the hash answers logged after a duplex entry predict
no digest reachable, in the snapshot at that entry, from the initial capacity or a digest its
input binds. -/
theorem noPrediction_snapshotAt {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    {s : Digest F} {x : List F} {a : Digest F × Vector F K}
    (hmem : (⟨.inl (s, x), a⟩ : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t) ∈ L)
    {r : Digest F} (hr : r = initCap ∨ r ∈ boundDigests offs capLen x) :
    (merkleCache (Bcs.snapshotAt L (s, x))).NoPrediction (merkleCache (Bcs.hashCacheOf L)) r := by
  obtain ⟨a₀, ha₀⟩ := Option.ne_none_iff_exists'.mp (Bcs.cacheOf_ne_none_of_mem hmem)
  obtain ⟨pre₀, post₀, hL₀, hfresh₀⟩ := exists_first_of_cacheOf ha₀
  have hsnap : Bcs.snapshotAt L (s, x) = Bcs.hashCacheOf pre₀ := by
    rw [hL₀]
    exact snapshotAt_eq a₀ hfresh₀
  rw [hsnap]
  have hle : ∀ t (u : Digest F), Bcs.cacheOf pre₀ (.inr t) = some u →
      Bcs.cacheOf L (.inr t) = some u := fun t u h ↦ hL₀ ▸ cacheOf_append_of_eq_some h _
  have hnew : ∀ t (y : Digest F), Bcs.cacheOf L (.inr t) = some y →
      (merkleCache (Bcs.hashCacheOf pre₀)).Known r y → Bcs.cacheOf pre₀ (.inr t) = some y := by
    intro t y h hk
    obtain ⟨pre, post, hL₁, hfresh⟩ := exists_first_of_cacheOf h
    have hsplit := hL₁.symm.trans hL₀
    rcases lt_trichotomy pre.length pre₀.length with hlt | heq | hgt
    · obtain ⟨mid, hmid⟩ := exists_mid_of_length_lt hsplit hlt
      rw [hmid]
      exact cacheOf_append_cons _ hfresh
    · exact absurd (congrArg Sigma.fst (eq_of_length_eq hsplit heq)) Sum.inr_ne_inl
    · obtain ⟨mid, hmid⟩ := exists_mid_of_length_lt hsplit.symm hgt
      refine absurd ?_ (not_mem_logDigests hL hL₁ hfresh)
      rcases hk with rfl | ⟨left, right, parent, hnode, hy⟩
      · rcases hr with rfl | hr
        · exact initCap_mem_logDigests pre
        · exact mem_logDigests_of_mem (hmid ▸ List.mem_append_right _ List.mem_cons_self)
            (e := ⟨.inl (s, x), a₀⟩) (List.mem_cons_of_mem _ hr)
      · change Bcs.cacheOf pre₀ (.inr (.inr (left, right))) = some parent at hnode
        refine mem_logDigests_of_mem (hmid ▸ List.mem_append_left _ (mem_of_cacheOf hnode))
          (e := ⟨.inr (.inr (left, right)), parent⟩) ?_
        rcases hy with rfl | rfl
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact {
    leaf_le := fun row y h ↦ hle (.inl row) y h
    node_le := fun left right y h ↦ hle (.inr (left, right)) y h
    leaf_new := fun row y h hk ↦ hnew (.inl row) y h hk
    node_new := fun left right y h hk ↦ hnew (.inr (left, right)) y h hk }

/-- **Stable extraction.** Without `HashBad`, the row extracted under the initial capacity or a
digest bound by a logged duplex input is the same from the snapshot at that input and from all
the logged hash answers. -/
theorem extractRow_snapshotAt {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    {s : Digest F} {x : List F} {a : Digest F × Vector F K}
    (hmem : (⟨.inl (s, x), a⟩ : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t) ∈ L)
    {r : Digest F} (hr : r = initCap ∨ r ∈ boundDigests offs capLen x) (k i : ℕ) :
    Merkle.extractRow (merkleCache (Bcs.snapshotAt L (s, x))) k i r =
      Merkle.extractRow (merkleCache (Bcs.hashCacheOf L)) k i r :=
  (Merkle.extractRow_eq_of_noPrediction _ _ r (noPrediction_snapshotAt hL hmem hr) k i).symm

/-- `extractRow_snapshotAt` for trees of mixed heights. -/
theorem extractGroup_snapshotAt {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    {s : Digest F} {x : List F} {a : Digest F × Vector F K}
    (hmem : (⟨.inl (s, x), a⟩ : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t) ∈ L)
    {r : Digest F} (hr : r = initCap ∨ r ∈ boundDigests offs capLen x) (inj : List ℕ)
    (top t i : ℕ) :
    Merkle.extractGroup (merkleCache (Bcs.snapshotAt L (s, x))) inj top t i r =
      Merkle.extractGroup (merkleCache (Bcs.hashCacheOf L)) inj top t i r :=
  (Merkle.extractGroup_eq_of_noPrediction _ _ inj r (noPrediction_snapshotAt hL hmem hr)
    top t i).symm

/-- The zero digest is the initial capacity. -/
theorem zero_eq_initCap : (0 : Digest F) = initCap :=
  Vector.ext fun i hi ↦ by rw [Vector.getElem_zero, initCap, Vector.getElem_replicate]

/-- An entry of a cap, or the zero digest past its end. -/
theorem getD_cap (cap : List (Digest F)) (j : ℕ) : cap.getD j 0 = initCap ∨ cap.getD j 0 ∈ cap := by
  rw [List.getD_eq_getElem?_getD]
  cases h : cap[j]? with
  | none => exact Or.inl zero_eq_initCap
  | some d => exact Or.inr (List.mem_of_getElem? h)

/-- `extractRow_snapshotAt` under a cap whose digests a logged duplex input binds. -/
theorem extractCapRow_snapshotAt {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    {s : Digest F} {x : List F} {a : Digest F × Vector F K}
    (hmem : (⟨.inl (s, x), a⟩ : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t) ∈ L)
    {cap : List (Digest F)} (hcap : ∀ d ∈ cap, d ∈ boundDigests offs capLen x) (k h i : ℕ) :
    Merkle.extractCapRow (merkleCache (Bcs.snapshotAt L (s, x))) k h i cap =
      Merkle.extractCapRow (merkleCache (Bcs.hashCacheOf L)) k h i cap :=
  extractRow_snapshotAt hL hmem ((getD_cap cap _).imp_right (hcap _)) _ _

/-- `extractCapRow_snapshotAt` for the columns of matrices of mixed heights. -/
theorem matColumnCap_snapshotAt {L : QueryLog (sumSpec F K)} (hL : ¬ HashBad offs capLen L)
    {s : Digest F} {x : List F} {a : Digest F × Vector F K}
    (hmem : (⟨.inl (s, x), a⟩ : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t) ∈ L)
    {cap : List (Digest F)} (hcap : ∀ d ∈ cap, d ∈ boundDigests offs capLen x)
    (capHeight top : ℕ) (hs ws : List ℕ) (t j m r : ℕ) :
    Merkle.matColumnCap (merkleCache (Bcs.snapshotAt L (s, x))) cap capHeight top hs ws t j m r =
      Merkle.matColumnCap (merkleCache (Bcs.hashCacheOf L)) cap capHeight top hs ws t j m r := by
  simp only [Merkle.matColumnCap, Merkle.matColumn]
  rw [extractGroup_snapshotAt hL hmem ((getD_cap cap _).imp_right (hcap _))]

end Stable

/-! ### Binding -/

section Climb
variable {d : ℕ} (hash : List F → Vector F d) (compress : Vector F d → Vector F d → Vector F d)
  (values : List (List F)) (dstar : Vector F d) (cached : Vector F d → Vector F d → Prop)

/-- A climb that does not end at `dstar` compresses only cached pairs, if compressing an uncached
pair or a pair with `dstar` gives `dstar`. -/
theorem climbPairs_cached [Zero F] (hfresh : ∀ a b, ¬ cached a b → compress a b = dstar)
    (hstuck : ∀ a b, (a = dstar ∨ b = dstar) → ¬ cached a b) :
    ∀ (path : List (Vector F d)) (leaf : Vector F d) (i padded : ℕ),
      Merkle.climb hash compress values path [] i padded leaf ≠ dstar →
        leaf ≠ dstar ∧ ∀ pair ∈ Merkle.climbPairs compress leaf i path, cached pair.1 pair.2
  | [], leaf, _, _, h => ⟨h, fun _ hp ↦ absurd hp List.not_mem_nil⟩
  | sib :: sibs, leaf, i, padded, h => by
    set pair := if i % 2 = 0 then (leaf, sib) else (sib, leaf) with hpair
    have hclimb : Merkle.climb hash compress values (sib :: sibs) [] i padded leaf =
        Merkle.climb hash compress values sibs [] (i / 2) (padded / 2)
          (compress pair.1 pair.2) := by
      by_cases hi : i % 2 = 0 <;> simp only [Merkle.climb, hpair, hi, ↓reduceIte]
    rw [hclimb] at h
    obtain ⟨hnext, hrest⟩ := climbPairs_cached hfresh hstuck sibs _ (i / 2) (padded / 2) h
    have hc : cached pair.1 pair.2 := by
      by_contra hc
      exact hnext (hfresh _ _ hc)
    refine ⟨fun hl ↦ hstuck pair.1 pair.2 ?_ hc, fun p hp ↦ ?_⟩
    · by_cases hi : i % 2 = 0 <;> simp only [hpair, hi, ↓reduceIte, hl, true_or, or_true]
    · simp only [Merkle.climbPairs, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hc
      · exact hrest p hp

/-- An accepted single-height opening climbs from the hash of the opened rows to the
commitment. -/
theorem climb_eq_of_verifyBatch [Zero F] [DecidableEq F] (root : Vector F d) (n k i : ℕ)
    (hn : 0 < n) (path : List (Vector F d))
    (hv : Merkle.verifyBatch hash compress root (List.replicate n (2 ^ k)) i values path = true) :
    Merkle.climb hash compress values path [] i (2 ^ k) (hash values.flatten) = root := by
  have hlog : Nat.log2 (2 ^ k).nextPowerOfTwo = k := Merkle.log2Ceil_two_pow k
  have hlen : path.length = k := by
    simp only [Merkle.verifyBatch, Merkle.heightGroups_replicate n _ hn, Bool.and_eq_true,
      beq_iff_eq, hlog] at hv
    exact hv.1.1.2
  have hdepth : path.reverse.length = (BinaryTree.SkeletonLeafIndex.ofNat k i).depth := by
    rw [List.length_reverse, hlen, BinaryTree.SkeletonLeafIndex.depth_ofNat]
  have hroot := ((Merkle.verifyBatch_iff hash compress root n k i hn values path ⟨_, hdepth⟩
    rfl).mp hv).2.2
  rwa [← Merkle.climb_eq_getPutativeRootWithHash hash compress values i (2 ^ k) _ k path _
    ⟨path.reverse, hdepth⟩ rfl rfl] at hroot

/-- An accepted opening of mixed heights climbs from the hash of its tallest rows to the
commitment. -/
theorem climb_eq_of_verifyBatch_mixed [Zero F] [DecidableEq F] (root : Vector F d)
    (hs : List ℕ) (i : ℕ) (path : List (Vector F d))
    (hv : Merkle.verifyBatch hash compress root hs i values path = true) :
    ∃ maxH tallest rest, Merkle.heightGroups hs = (maxH, tallest) :: rest ∧
      Merkle.climb hash compress values path rest i maxH.nextPowerOfTwo
        (Merkle.hashRows hash values tallest) = root := by
  unfold Merkle.verifyBatch at hv
  split at hv
  · exact absurd hv Bool.false_ne_true
  · rename_i maxH tallest rest hG
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    exact ⟨maxH, tallest, rest, hG, hv.2⟩

end Climb

section Binding
variable [BaseField F] {offs : List ℕ} {capLen : ℕ}

/-- The logged leaf hash of `row`, `dstar` if it is not logged. -/
def logHash (L : QueryLog (sumSpec F K)) (dstar : Digest F) (row : List F) : Digest F :=
  (Bcs.hashCacheOf L (.inl row)).getD dstar

/-- The logged compression of `left, right`, `dstar` if it is not logged. -/
def logCompress (L : QueryLog (sumSpec F K)) (dstar : Digest F) (left right : Digest F) :
    Digest F :=
  (Bcs.hashCacheOf L (.inr (left, right))).getD dstar

/-- The logged answers of the verifier's oracles: `dstar` for a hash query that is not logged,
and `dstar` with zero samples for such a duplex call. -/
def logAnswer (L : QueryLog (sumSpec F K)) (dstar : Digest F) : (q : Query F) → Answer K q
  | .duplex cap input => (Bcs.cacheOf L (.inl (cap, input))).getD (dstar, Vector.replicate K 0)
  | .leaf row => logHash L dstar row
  | .node left right => logCompress L dstar left right

theorem idealOf_logAnswer_hash (L : QueryLog (sumSpec F K)) (dstar : Digest F) :
    (idealOf (logAnswer L dstar)).hash = logHash L dstar := rfl

theorem idealOf_logAnswer_compress (L : QueryLog (sumSpec F K)) (dstar : Digest F) :
    (idealOf (logAnswer L dstar)).compress = logCompress L dstar := rfl

/-- A leaf hash answered other than `dstar` is logged. -/
theorem leaf_logHash {L : QueryLog (sumSpec F K)} {dstar : Digest F} {row : List F}
    (h : logHash L dstar row ≠ dstar) :
    (merkleCache (Bcs.hashCacheOf L)).leaf row (logHash L dstar row) := by
  show Bcs.hashCacheOf L (.inl row) = some ((Bcs.hashCacheOf L (.inl row)).getD dstar)
  unfold logHash at h
  cases hc : Bcs.hashCacheOf L (.inl row) with
  | none => rw [hc] at h; exact absurd rfl h
  | some v => rfl

/-- A logged compression is cached at its logged answer. -/
theorem node_logCompress {L : QueryLog (sumSpec F K)} {dstar a b : Digest F}
    (h : Bcs.hashCacheOf L (.inr (a, b)) ≠ none) :
    (merkleCache (Bcs.hashCacheOf L)).node a b (logCompress L dstar a b) := by
  show Bcs.hashCacheOf L (.inr (a, b)) = some ((Bcs.hashCacheOf L (.inr (a, b))).getD dstar)
  cases hc : Bcs.hashCacheOf L (.inr (a, b)) with
  | none => exact absurd hc h
  | some v => rfl

/-- A compression with `dstar`, a digest outside the log, is not logged. -/
theorem hashCacheOf_eq_none_of_dstar {L : QueryLog (sumSpec F K)} {dstar : Digest F}
    (hdstar : dstar ∉ logDigests offs capLen L) {a b : Digest F} (hab : a = dstar ∨ b = dstar) :
    Bcs.hashCacheOf L (.inr (a, b)) = none := by
  cases hc : Bcs.hashCacheOf L (.inr (a, b)) with
  | none => rfl
  | some v =>
    rw [hashCacheOf_apply] at hc
    refine absurd (mem_logDigests_of_mem (mem_of_cacheOf hc) ?_) hdstar
    rcases hab with rfl | rfl
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- An uncached compression answers `dstar`. -/
theorem logCompress_of_eq_none {L : QueryLog (sumSpec F K)} {dstar a b : Digest F}
    (h : Bcs.hashCacheOf L (.inr (a, b)) = none) : logCompress L dstar a b = dstar := by
  unfold logCompress
  rw [h]
  rfl

/-- **Binding.** Without `HashBad`, an opening of `n > 0` matrices of height `2 ^ k` accepted on
the logged answers, against any digest but `dstar`, a digest outside the log, opens the rows
extracted from the logged hash answers. -/
theorem extractRow_of_logVerifyBatch {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs capLen L) {dstar : Digest F} (hdstar : dstar ∉ logDigests offs capLen L)
    {root : Digest F} (hroot : root ≠ dstar) (n k i : ℕ) (hn : 0 < n) (values : List (List F))
    (path : List (Digest F))
    (hv : Merkle.verifyBatch (logHash L dstar) (logCompress L dstar) root
      (List.replicate n (2 ^ k)) i values path = true) :
    Merkle.extractRow (merkleCache (Bcs.hashCacheOf L)) k i root = some values.flatten := by
  have hclimb := climb_eq_of_verifyBatch _ _ values root n k i hn path hv
  obtain ⟨hleaf, hnodes⟩ := climbPairs_cached (logHash L dstar) (logCompress L dstar) values
    dstar (fun a b ↦ Bcs.hashCacheOf L (.inr (a, b)) ≠ none)
    (fun a b h ↦ logCompress_of_eq_none (not_not.mp h))
    (fun a b hab h ↦ h (hashCacheOf_eq_none_of_dstar hdstar hab)) path _ i (2 ^ k)
    (by rw [hclimb]; exact hroot)
  exact Merkle.extractRow_eq_of_verifyBatch _ (hashCache_injective hL) _ _ root n k i hn values
    path hv (leaf_logHash hleaf) fun pair hp ↦ node_logCompress (hnodes pair hp)

/-- **Binding at mixed heights.** Without `HashBad`, an opening of matrices of heights
`2 ^ j ≤ 2 ^ top`, some of height `2 ^ top`, accepted on the logged answers against any digest
but `dstar`, a digest outside the log, opens every group's rows extracted from the logged hash
answers. -/
theorem extractGroup_of_logVerifyBatch {L : QueryLog (sumSpec F K)}
    (hL : ¬ HashBad offs capLen L) {dstar : Digest F} (hdstar : dstar ∉ logDigests offs capLen L)
    {root : Digest F} (hroot : root ≠ dstar) (top : ℕ) (hs : List ℕ)
    (hpow : ∀ h ∈ hs, ∃ j ≤ top, h = 2 ^ j)
    (htop : 2 ^ top ∈ hs) (i : ℕ) (values : List (List F)) (path : List (Digest F))
    (hv : Merkle.verifyBatch (logHash L dstar) (logCompress L dstar) root hs i values path =
      true) :
    ∀ g ∈ Merkle.heightGroups hs, ∀ l, g.1 = 2 ^ l →
      Merkle.extractGroup (merkleCache (Bcs.hashCacheOf L)) (Merkle.injLevels top hs) top l
        (i >>> (top - l)) root = some (g.2.flatMap fun m ↦ values.getD m []) := by
  have hnode : ∀ a b, logCompress L dstar a b ≠ dstar →
      (merkleCache (Bcs.hashCacheOf L)).node a b (logCompress L dstar a b) := fun a b h ↦
    node_logCompress fun hc ↦ h (logCompress_of_eq_none hc)
  have hstuck : ∀ a b, (a = dstar ∨ b = dstar) → logCompress L dstar a b = dstar :=
    fun a b hab ↦ logCompress_of_eq_none (hashCacheOf_eq_none_of_dstar hdstar hab)
  obtain ⟨maxH, tallest, rest, hG, hclimb⟩ :=
    climb_eq_of_verifyBatch_mixed _ _ values root hs i path hv
  obtain ⟨keys, hk, hmem, hG'⟩ := Merkle.heightGroups_eq hs
  have hmax : maxH = 2 ^ top := by
    rw [hG'] at hG
    rcases keys with _ | ⟨a, ks⟩
    · exact absurd hG (by simp only [List.map_nil, reduceCtorEq, not_false_eq_true])
    · simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hG
      rw [← hG.1.1]
      obtain ⟨j, hj, rfl⟩ := hpow a ((hmem a).mp List.mem_cons_self)
      rcases List.mem_cons.mp ((hmem _).mpr htop) with h | h
      · exact h.symm
      · have := List.rel_of_pairwise_cons hk h
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj
        omega
  rw [hmax, Merkle.nextPowerOfTwo_two_pow] at hclimb
  obtain ⟨hx, hcc⟩ := Merkle.climbCached_of_fresh (merkleCache (Bcs.hashCacheOf L))
    (logHash L dstar) (logCompress L dstar) values dstar hnode (fun row h ↦ leaf_logHash h)
    hstuck path rest i _ _ (by rw [hclimb]; exact hroot)
  refine Merkle.extractGroup_of_verifyBatch _ _ _ values (hashCache_injective hL) root top hs
    hpow htop i path hv ?_ ?_
  · rw [hG]
    intro g hg
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact leaf_logHash hx
  · rw [hG]
    intro g hg
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg
    subst hg
    exact hcc

end Binding

/-! ### The probability of a clash -/

section Probability
variable {offs : List ℕ} {capLen : ℕ}

/-- A fresh answer `u` to `t` after the log `pre` is bad: a hash answer with a known digest. -/
def StepBad [Zero F] (offs : List ℕ) (capLen : ℕ) (pre : QueryLog (sumSpec F K)) :
    (t : (sumSpec F K).Domain) → (sumSpec F K).Range t → Prop
  | .inl _, _ => False
  | .inr _, u => u ∈ logDigests offs capLen pre

theorem hashBad_append_singleton [Zero F] {L : QueryLog (sumSpec F K)}
    {e : (t : (sumSpec F K).Domain) × (sumSpec F K).Range t}
    (h : HashBad offs capLen (L ++ [e])) :
    HashBad offs capLen L ∨ (e.1 ∉ L.map Sigma.fst ∧ StepBad offs capLen L e.1 e.2) := by
  obtain ⟨pre, t, u, post, hsplit, hfresh, hu⟩ := h
  rcases List.eq_nil_or_concat' post with rfl | ⟨post', y, rfl⟩
  · obtain ⟨rfl, he⟩ := List.append_inj' hsplit rfl
    obtain rfl := (List.cons.inj he).1
    exact Or.inr ⟨hfresh, hu⟩
  · refine Or.inl ⟨pre, t, u, post', ?_, hfresh, hu⟩
    rw [← List.cons_append, ← List.append_assoc] at hsplit
    exact (List.append_inj' hsplit rfl).1

/-- A union bound: a uniform sample lands in a list with probability at most its length over the
number of values. -/
theorem prEvent_uniform_mem_le {β : Type} [SampleableType β] (known : List β) :
    Pr{let u ← $ᵗ β}[u ∈ known] ≤ known.length * (Nat.card β : ℝ≥0∞)⁻¹ := by
  induction known with
  | nil =>
    exact (prEvent_mono _ _ (fun _ ↦ False) fun _ hu ↦ List.not_mem_nil hu).trans
      (by simp only [prEvent_false, zero_le])
  | cons x known ih =>
    refine (prEvent_mono _ _ _ fun u hu ↦ List.mem_cons.mp hu).trans ?_
    refine (prEvent_or_le _ _ _).trans ?_
    rw [List.length_cons, Nat.cast_succ, add_mul, one_mul]
    exact (add_le_add (SampleableType.prEvent_uniformSample_eq_singleton_natCard x).le ih).trans_eq
      (add_comm _ _)

variable [BaseField F]

/-- A fresh answer is bad with probability at most the number of digests known before it over
the number of digests. -/
theorem prEvent_stepBad_le (hB : 0 < offs.length * capLen) (pre : QueryLog (sumSpec F K))
    (t : (sumSpec F K).Domain) :
    Pr{let u ← $ᵗ (sumSpec F K).Range t}[StepBad offs capLen pre t u] ≤
      ((1 + (2 + offs.length * capLen) * pre.length : ℕ) : ℝ≥0∞) *
        (Nat.card (Digest F) : ℝ≥0∞)⁻¹ := by
  rcases t with q | t
  · exact (prEvent_mono _ _ (fun _ ↦ False) fun _ hu ↦ hu).trans
      (by simp only [prEvent_false, zero_le])
  · exact (prEvent_uniform_mem_le (β := (sumSpec F K).Range (.inr t))
      (logDigests offs capLen pre)).trans
      (mul_le_mul' (Nat.cast_le.mpr (length_logDigests_le hB pre)) le_rfl)

/-- The clash bound from any log without `HashBad`, of length at most `N` minus the query
budget `n`. -/
theorem prEvent_hashBad_run_le (hB : 0 < offs.length * capLen) (N : ℕ) {α : Type}
    (P : OracleComp (unifSpec + sumSpec F K) α) (n : ℕ)
    (hn : IsQueryBoundP P (fun t ↦ t.isRight = true) n) (L₀ : QueryLog (sumSpec F K))
    (hL₀ : ¬ HashBad offs capLen L₀) (hlen : L₀.length + n ≤ N) :
    Pr{let z ← (simulateQ Bcs.realImpl P).run L₀}[HashBad offs capLen z.2] ≤
      n * (((2 + offs.length * capLen) * N : ℕ) * (Nat.card (Digest F) : ℝ≥0∞)⁻¹) := by
  induction P using OracleComp.inductionOn generalizing n L₀ with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, hL₀, prEvent_pure_prop, ↓reduceIte,
      zero_le]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    obtain ⟨hpos, hk⟩ := hn
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with m | t
    · rw [Bcs.realImpl_run_unif, bind_map_left]
      exact prEvent_bind_le_of_forall_le _ _ _ fun u ↦
        ih u n (by simpa only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte] using hk u) L₀
          hL₀ hlen
    · have hn1 : 0 < n := by simpa only [Sum.isRight_inr, not_true_eq_false, false_or] using hpos
      have hk' : ∀ u, IsQueryBoundP (k u) (fun t ↦ t.isRight = true) (n - 1) := fun u ↦ by
        simpa only [Sum.isRight_inr, ↓reduceIte] using hk u
      set ε : ℝ≥0∞ := ((2 + offs.length * capLen) * N : ℕ) * (Nat.card (Digest F) : ℝ≥0∞)⁻¹
      have hsucc : (n : ℝ≥0∞) = 1 + ((n - 1 : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        congr 1
        omega
      cases hc : Bcs.cacheOf L₀ t with
      | some u =>
        rw [Bcs.realImpl_run_of_some hc, pure_bind]
        refine (ih u (n - 1) (hk' u) L₀ hL₀ (by omega)).trans ?_
        rw [hsucc]
        exact mul_le_mul_left (le_add_self) _
      | none =>
        rw [Bcs.realImpl_run_of_none hc, bind_map_left]
        refine (prEvent_bind_le_prEvent_add _ _ (StepBad offs capLen L₀ t) _ fun u hu ↦
          ih u (n - 1) (hk' u) _ (fun hbad ↦ ?_) ?_).trans ?_
        · rcases hashBad_append_singleton hbad with h | ⟨-, h⟩
          · exact hL₀ h
          · exact hu h
        · simp only [List.length_append, List.length_singleton]
          omega
        · have hstep : Pr{let u ← $ᵗ (sumSpec F K).Range t}[StepBad offs capLen L₀ t u] ≤ ε :=
            (prEvent_stepBad_le hB L₀ t).trans (mul_le_mul' (Nat.cast_le.mpr (by
              have h1 : L₀.length + 1 ≤ N := by omega
              have h2 := Nat.mul_le_mul_left (2 + offs.length * capLen) h1
              rw [Nat.mul_succ] at h2
              omega)) le_rfl)
          rw [hsucc, add_mul, one_mul]
          exact add_le_add hstep le_rfl

/-- The bound on digest clashes: `(2 + m capLen) q² / |F|⁸`, for `q` oracle queries and duplex
inputs binding `m` caps of up to `capLen` digests each. -/
noncomputable def hashBadError (F : Type) (capLen m q : ℕ) : ℝ≥0∞ :=
  (2 + m * capLen) * q ^ 2 / (Nat.card F : ℝ≥0∞) ^ 8

/-- **Digest clashes.** A program making at most `q` queries to the verifier's oracles, run against
the logged real oracles, logs a hash answer with a digest known before it with probability at most
`hashBadError F capLen offs.length q = (2 + |offs| capLen) q² / |F|⁸`: each fresh hash answer is
uniform, and fewer than `(2 + |offs| capLen) q` digests are known before it. -/
theorem prEvent_hashBad_le (hB : 0 < offs.length * capLen) {α : Type}
    (P : OracleComp (unifSpec + sumSpec F K) α) (q : ℕ)
    (hq : IsQueryBoundP P (fun t ↦ t.isRight = true) q) :
    Pr{let z ← (simulateQ Bcs.realImpl P).run []}[HashBad offs capLen z.2] ≤
      hashBadError F capLen offs.length q := by
  refine (prEvent_hashBad_run_le hB q P q hq [] not_hashBad_nil
    (by rw [List.length_nil, Nat.zero_add])).trans (le_of_eq ?_)
  rw [hashBadError, natCard_digest, div_eq_mul_inv]
  push_cast
  ring

end Probability

end CompStark.Fs
