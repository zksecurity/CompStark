/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Ni.Rounds
public import CompStark.Fs.DigestClash

/-! # Logs without digest clashes

The digest of an answer (`digestOf`) is a hash, or a duplex call's new capacity; the digests of a
key (`keyDigests`) are a compression's children, a duplex call's capacity and the digest its input
binds (`boundDigest`). A log is `NoClash` when no query, at its first occurrence, gets an answer
whose digest is the initial capacity, an earlier answer's or one in an earlier or its own key
(B's `DigestClash`). Then, with every query answered by one table `answer`:

* digests are unique (`eq_of_digestOf_eq`), so the duplex calls' capacities are injective
  (`capsInjective`) and so are the hash queries (`logCache_injective`);
* a digest in a key is answered before the key is first queried (`idx_lt_of_mem_keyDigests`):
  the rounds of a duplex chain are first queried in order (`hasRounds_take`), and extraction under
  a digest some key binds does not change after that key is first queried
  (`noPrediction_take`).

Positions are first occurrences: `idx log t` is the index of the first query of `t` in `log`.
-/

@[expose] public section
namespace CompStark.Ni
open CompStark.Stark CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp

local notation "F" => KoalaBear.Fast.Field

variable {K : Nat}

/-- The digest of an answer: the hash, or the duplex call's new capacity. -/
def digestOf : (t : Query) → Answer K t → Digest
  | .duplex .., u => u.1
  | .leaf _, u => u
  | .node .., u => u

/-- The digests in a key: a compression's children, and a duplex call's capacity and the digest
its input binds. -/
def keyDigests : Query → List Digest
  | .duplex cap input => [cap, boundDigest cap input]
  | .leaf _ => []
  | .node left right => [left, right]

theorem length_keyDigests_le (t : Query) : (keyDigests t).length ≤ 2 := by
  cases t <;> simp only [keyDigests, List.length_cons, List.length_nil] <;> omega

/-- The answer `u` to `t` after the queries `pre` has a digest known before: the initial capacity,
an earlier answer's, or one in an earlier key or in `t`. -/
abbrev Clash (pre : QueryLog (spec K)) (t : Query) (u : Answer K t) : Prop :=
  DigestClash digestOf keyDigests [initCap] pre t u

/-- The first position of the key `t` in `log`. -/
def idx (log : QueryLog (spec K)) (t : Query) : Nat := (log.map Sigma.fst).idxOf t

section Log
variable (answer : (q : Query) → Answer K q) (log : QueryLog (spec K))

/-- No query of `log` gets, at its first occurrence, an answer with a known digest. -/
def NoClash : Prop :=
  ∀ p (hp : p < log.length), log[p].1 ∉ (log.take p).map Sigma.fst →
    ¬ Clash (log.take p) log[p].1 log[p].2

variable {answer log}

theorem idx_lt {t : Query} (ht : t ∈ log.map Sigma.fst) : idx log t < log.length := by
  have := List.idxOf_lt_length_of_mem ht
  rwa [List.length_map] at this

theorem getElem_idx_fst {t : Query} (ht : t ∈ log.map Sigma.fst) :
    (log[idx log t]'(idx_lt ht)).1 = t := by
  have h := List.getElem_idxOf (List.idxOf_lt_length_of_mem ht)
  simp only [List.getElem_map] at h
  exact h

theorem mem_take_iff {t : Query} (ht : t ∈ log.map Sigma.fst) (p : Nat) :
    t ∈ (log.take p).map Sigma.fst ↔ idx log t < p := by
  rw [List.map_take, List.mem_take_iff_idxOf_lt ht]
  rfl

theorem not_mem_take_idx {t : Query} (ht : t ∈ log.map Sigma.fst) :
    t ∉ (log.take (idx log t)).map Sigma.fst := by
  rw [mem_take_iff ht]
  exact lt_irrefl _

/-- A consistent log holds the answer of each of its keys. -/
theorem mk_mem_of_consistent (hcons : Consistent answer log) {t : Query}
    (ht : t ∈ log.map Sigma.fst) : (⟨t, answer t⟩ : (q : Query) × Answer K q) ∈ log := by
  obtain ⟨⟨t', a⟩, he, rfl⟩ := List.mem_map.mp ht
  have ha : a = answer t' := hcons _ he
  subst ha
  exact he

theorem consistent_take (hcons : Consistent answer log) (p : Nat) :
    Consistent answer (log.take p) := fun e he ↦ hcons e (List.mem_of_mem_take he)

theorem getElem_snd (hcons : Consistent answer log) (p : Nat) (hp : p < log.length) :
    log[p].2 = answer log[p].1 := hcons _ (List.getElem_mem hp)

/-- A digest known before position `p` gives a clash at the first occurrence at `p`. -/
theorem clash_of_known (hcons : Consistent answer log) (hclash : NoClash log)
    (p : Nat) (hp : p < log.length) (hfresh : log[p].1 ∉ (log.take p).map Sigma.fst)
    (hknown : digestOf log[p].1 (answer log[p].1) ∈
      knownDigests digestOf keyDigests [initCap] (log.take p) log[p].1) : False := by
  refine hclash p hp hfresh ?_
  unfold Clash DigestClash
  rw [getElem_snd hcons p hp]
  exact hknown

/-- An entry before position `p` contributes its digests to the known ones. -/
theorem mem_known_of_mem (e : (q : Query) × Answer K q) (pre : QueryLog (spec K)) (he : e ∈ pre)
    (t : Query) (d : Digest) (hd : d ∈ digestOf e.1 e.2 :: keyDigests e.1) :
    d ∈ knownDigests digestOf keyDigests [initCap] pre t := by
  unfold knownDigests
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hd⟩))

theorem getElem_mem_take (p i : Nat) (hi : i < p) (hl : i < log.length) :
    log[i] ∈ log.take p := by
  have h : i < (log.take p).length := by rw [List.length_take]; omega
  rw [← List.getElem_take (h := h)]
  exact List.getElem_mem h

variable (hcons : Consistent answer log) (hclash : NoClash log)
include hcons hclash

/-- **No prediction.** A digest in a key was answered before the key's first query. -/
theorem idx_lt_of_mem_keyDigests {t t' : Query} (ht : t ∈ log.map Sigma.fst)
    (ht' : t' ∈ log.map Sigma.fst) {d : Digest} (hd : d ∈ keyDigests t)
    (hdig : digestOf t' (answer t') = d) : idx log t' < idx log t := by
  by_contra hle
  have hle : idx log t ≤ idx log t' := not_lt.mp hle
  set p := idx log t'
  have hp := idx_lt ht'
  have hfst := getElem_idx_fst ht'
  refine clash_of_known hcons hclash p hp (by rw [hfst]; exact not_mem_take_idx ht') ?_
  rw [hfst, hdig]
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · have hmem := getElem_mem_take p (idx log t) hlt (idx_lt ht)
    refine mem_known_of_mem _ _ hmem t' d (List.mem_cons_of_mem _ ?_)
    rw [getElem_idx_fst ht]
    exact hd
  · have htt : t = t' := by
      rw [← getElem_idx_fst ht, ← hfst]
      simp only [p, heq]
    subst htt
    unfold knownDigests
    exact List.mem_append_right _ hd

/-- **No collision.** Distinct keys of the log have distinct digests. -/
theorem eq_of_digestOf_eq {t t' : Query} (ht : t ∈ log.map Sigma.fst)
    (ht' : t' ∈ log.map Sigma.fst) (h : digestOf t (answer t) = digestOf t' (answer t')) :
    t = t' := by
  by_contra hne
  have hidx : idx log t ≠ idx log t' := fun he ↦ hne (by
    rw [← getElem_idx_fst ht, ← getElem_idx_fst ht']
    simp only [he])
  wlog hlt : idx log t < idx log t' generalizing t t'
  · exact this ht' ht h.symm (Ne.symm hne) (Ne.symm hidx) (by omega)
  set p := idx log t'
  have hp := idx_lt ht'
  have hfst := getElem_idx_fst ht'
  refine clash_of_known hcons hclash p hp (by rw [hfst]; exact not_mem_take_idx ht') ?_
  rw [hfst]
  have hmem := getElem_mem_take p (idx log t) hlt (idx_lt ht)
  refine mem_known_of_mem _ _ hmem t' _ ?_
  rw [getElem_snd hcons _ (idx_lt ht), getElem_idx_fst ht, h]
  exact List.mem_cons_self

/-- No answer's digest is the initial capacity. -/
theorem digestOf_ne_initCap {t : Query} (ht : t ∈ log.map Sigma.fst) :
    digestOf t (answer t) ≠ initCap := by
  intro h
  set p := idx log t
  have hfst := getElem_idx_fst ht
  refine clash_of_known hcons hclash p (idx_lt ht) (by rw [hfst]; exact not_mem_take_idx ht) ?_
  rw [hfst, h]
  unfold knownDigests
  exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)

/-- The duplex calls of a part of the log answer distinct capacities, none the initial one. -/
theorem capsInjective (sub : QueryLog (spec K))
    (hsub : ∀ t ∈ sub.map Sigma.fst, t ∈ log.map Sigma.fst) : CapsInjective answer sub := by
  intro c input hmem
  refine ⟨digestOf_ne_initCap hcons hclash (hsub _ hmem), fun c' input' hmem' heq ↦ ?_⟩
  have := eq_of_digestOf_eq hcons hclash (hsub _ hmem) (hsub _ hmem') heq
  simp only [Query.duplex.injEq] at this
  exact this

/-- The hash queries of the log are injective. -/
theorem logCache_injective : (logCache log).Injective where
  leaf row row' y h h' := by
    have hy : y = answer (.leaf row) := hcons _ h
    have hy' : y = answer (.leaf row') := hcons _ h'
    have := eq_of_digestOf_eq hcons hclash (List.mem_map_of_mem (f := Sigma.fst) h)
      (List.mem_map_of_mem (f := Sigma.fst) h') (by
        show answer (.leaf row) = answer (.leaf row')
        rw [← hy, ← hy'])
    simp only [Query.leaf.injEq] at this
    exact this
  node left right left' right' y h h' := by
    have hy : y = answer (.node left right) := hcons _ h
    have hy' : y = answer (.node left' right') := hcons _ h'
    have := eq_of_digestOf_eq hcons hclash (List.mem_map_of_mem (f := Sigma.fst) h)
      (List.mem_map_of_mem (f := Sigma.fst) h') (by
        show answer (.node left right) = answer (.node left' right')
        rw [← hy, ← hy'])
    simp only [Query.node.injEq] at this
    exact this

/-- The rounds of a duplex chain in the log are first queried in order. -/
theorem idx_keyAt_lt (blocks : List (List F)) (n : Nat)
    (hkeys : ∀ j < n, keyAt answer blocks j ∈ log.map Sigma.fst) :
    ∀ j j', j < j' → j' < n → idx log (keyAt answer blocks j) < idx log (keyAt answer blocks j')
  | j, j' + 1, hj, hn => by
    have hstep : idx log (keyAt answer blocks j') < idx log (keyAt answer blocks (j' + 1)) :=
      idx_lt_of_mem_keyDigests hcons hclash (hkeys _ hn) (hkeys j' (by omega))
        (d := capAt answer blocks (j' + 1)) (by simp only [keyAt, keyDigests, List.mem_cons,
          true_or]) rfl
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
    · exact (idx_keyAt_lt blocks n hkeys j j' hlt (by omega)).trans hstep
    · exact hstep

/-- The log before a round's first query holds the rounds before it. -/
theorem hasRounds_take (blocks : List (List F)) (n : Nat)
    (hkeys : ∀ j < n, keyAt answer blocks j ∈ log.map Sigma.fst) (i : Nat) (hi : i < n) :
    HasRounds answer (log.take (idx log (keyAt answer blocks i))) blocks i := fun j hj ↦
  (mem_take_iff (hkeys j (by omega)) _).mpr (idx_keyAt_lt hcons hclash blocks n hkeys j i hj hi)

/-- **Stable extraction.** Extraction under a digest bound by a key of the log does not change
after that key's first query. -/
theorem noPrediction_take (root : Digest) (t₀ : Query) (ht₀ : t₀ ∈ log.map Sigma.fst)
    (hroot : root ∈ keyDigests t₀) (p p' : Nat) (hp : idx log t₀ ≤ p) (hpp' : p ≤ p') :
    (logCache (log.take p)).NoPrediction (logCache (log.take p')) root := by
  have hsub : ∀ e ∈ log.take p, e ∈ log.take p' := fun e he ↦ by
    rw [show log.take p = (log.take p').take p by rw [List.take_take, Nat.min_eq_left hpp']]
      at he
    exact List.mem_of_mem_take he
  -- a key of `log` answering a reachable digest is first queried before `p`
  have hbefore : ∀ t ∈ log.map Sigma.fst, (logCache (log.take p)).Known root
      (digestOf t (answer t)) → idx log t < p := by
    intro t ht hk
    rcases hk with h | ⟨left, right, parent, hnode, hy⟩
    · exact (idx_lt_of_mem_keyDigests hcons hclash ht₀ ht hroot h).trans_le hp
    · have hmem : Query.node left right ∈ (log.take p).map Sigma.fst :=
        List.mem_map_of_mem (f := Sigma.fst) hnode
      have hlog : Query.node left right ∈ log.map Sigma.fst :=
        List.mem_map_of_mem (f := Sigma.fst) (List.mem_of_mem_take hnode)
      refine (idx_lt_of_mem_keyDigests hcons hclash hlog ht (d := digestOf t (answer t)) ?_
        rfl).trans ((mem_take_iff hlog p).mp hmem)
      rcases hy with h | h <;> simp only [keyDigests, h, List.mem_cons, List.not_mem_nil,
        or_false, true_or, or_true]
  have hnew : ∀ t (y : Answer K t), (⟨t, y⟩ : (q : Query) × Answer K q) ∈ log.take p' →
      (logCache (log.take p)).Known root (digestOf t y) →
        (⟨t, y⟩ : (q : Query) × Answer K q) ∈ log.take p := by
    intro t y he hk
    have he' := List.mem_of_mem_take he
    have hy : y = answer t := hcons _ he'
    subst hy
    have ht : t ∈ log.map Sigma.fst := List.mem_map_of_mem (f := Sigma.fst) he'
    exact mk_mem_of_consistent (consistent_take hcons p)
      ((mem_take_iff ht p).mpr (hbefore t ht hk))
  exact {
    leaf_le := fun row y h ↦ hsub _ h
    node_le := fun left right y h ↦ hsub _ h
    leaf_new := fun row y h hk ↦ hnew (.leaf row) y h hk
    node_new := fun left right y h hk ↦ hnew (.node left right) y h hk }

end Log

end CompStark.Ni
