/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Fs.FreshQuery
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! # Digest collisions and predictions

A random oracle whose answers carry a digest (a hash value, or the new capacity of a duplex)
should never answer a fresh query with a digest seen before: one already answered (a
collision), one occurring in a key queried so far (a prediction: the key was formed before its
preimage was queried), or one of a few fixed digests such as the initial capacity. This is the
bad event `DigestClash` for `prEvent_exists_fresh_bad_le`:

* `prEvent_digestClash_le`: after `p` queries, with at most `m` digests in each key and digests
  of uniform answers uniform, a fresh answer clashes with probability at most
  `(|avoid| + (m + 1) p + m) / |Digest|`.
* `prEvent_exists_fresh_digestClash_le`: over an adaptive run of at most `n` queries, with at
  most one fixed digest, some fresh answer clashes with probability at most
  `(m + 1) n² / |Digest|`; for two digests per key, `3 n² / |Digest|`.

`hdigest`, uniform digests of uniform answers, holds for answers that are digests
(`SampleableType.prEvent_uniformSample_eq_singleton`) or pairs of a digest and more
(`prEvent_uniformSample_fst_eq`).
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

variable {D Digest α : Type} {R : D → Type}

/-- The digests that a fresh answer to the key `t` after the queries `pre` must avoid: the fixed
`avoid`, the digests answered in `pre`, and the digests occurring in the keys of `pre` and in
`t`. -/
def knownDigests (digest : (t : D) → R t → Digest) (keyDigests : D → List Digest)
    (avoid : List Digest) (pre : QueryLog (ofFn R)) (t : D) : List Digest :=
  avoid ++ pre.flatMap (fun q => digest q.1 q.2 :: keyDigests q.1) ++ keyDigests t

/-- The answer `u` to the key `t` after the queries `pre` has a known digest. -/
def DigestClash (digest : (t : D) → R t → Digest) (keyDigests : D → List Digest)
    (avoid : List Digest) (pre : QueryLog (ofFn R)) (t : D) (u : R t) : Prop :=
  digest t u ∈ knownDigests digest keyDigests avoid pre t

theorem length_knownDigests_le (digest : (t : D) → R t → Digest)
    (keyDigests : D → List Digest) (m : ℕ) (hkey : ∀ t, (keyDigests t).length ≤ m)
    (avoid : List Digest) (pre : QueryLog (ofFn R)) (t : D) :
    (knownDigests digest keyDigests avoid pre t).length ≤
      avoid.length + (m + 1) * pre.length + m := by
  have hflat : (pre.flatMap fun q => digest q.1 q.2 :: keyDigests q.1).length ≤
      (m + 1) * pre.length := by
    induction pre with
    | nil => simp only [List.flatMap_nil, List.length_nil, mul_zero, le_refl]
    | cons q pre ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have := hkey q.1
        rw [Nat.mul_succ]
        omega
  simp only [knownDigests, List.length_append]
  have := hkey t
  omega

/-- A union bound: a digest that hits each value with probability at most `δ` lands in a list
with probability at most its length times `δ`. -/
theorem prEvent_mem_le {β : Type} (mx : ProbComp β) (f : β → Digest) (δ : ℝ≥0∞)
    (hδ : ∀ x, Pr{let b ← mx}[f b = x] ≤ δ) (known : List Digest) :
    Pr{let b ← mx}[f b ∈ known] ≤ known.length * δ := by
  induction known with
  | nil => simp only [List.not_mem_nil, prEvent_false, zero_le]
  | cons x known ih =>
      simp only [List.mem_cons, List.length_cons, Nat.cast_succ, add_mul, one_mul]
      exact (prEvent_or_le _ _ _).trans ((add_le_add (hδ x) ih).trans_eq (add_comm _ _))

variable [Fintype Digest]

/-- The digest of a uniform answer `(digest, rest)` hits a fixed value with probability
`1 / |Digest|`. -/
theorem prEvent_uniformSample_fst_eq [SampleableType Digest] {β : Type} [SampleableType β]
    (x : Digest) : Pr{let u ← $ᵗ (Digest × β)}[u.1 = x] = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_fst (p := (· = x)),
    SampleableType.prEvent_uniformSample_eq_singleton]

variable [∀ d, SampleableType (R d)]

/-- A fresh answer whose digest is uniform clashes after `pre` with probability at most
`(|avoid| + (m + 1) |pre| + m) / |Digest|`, for at most `m` digests per key. -/
theorem prEvent_digestClash_le (digest : (t : D) → R t → Digest)
    (hdigest : ∀ t x, Pr{let u ← $ᵗ R t}[digest t u = x] ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹)
    (keyDigests : D → List Digest) (m : ℕ) (hkey : ∀ t, (keyDigests t).length ≤ m)
    (avoid : List Digest) (pre : QueryLog (ofFn R)) (t : D) :
    Pr{let u ← $ᵗ R t}[DigestClash digest keyDigests avoid pre t u] ≤
      (avoid.length + (m + 1) * pre.length + m : ℕ) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
  (prEvent_mem_le _ (digest t) _ (hdigest t) _).trans <| by
    gcongr
    exact length_knownDigests_le digest keyDigests m hkey avoid pre t

variable [DecidableEq D]

/-- **Digest collisions and predictions.** If the event forces a fresh query whose answer
clashes with the digests known before it, an adaptive computation making at most `n` queries
triggers it against a lazy random oracle with probability at most `(m + 1) n² / |Digest|`, for
at most one fixed digest, at most `m` digests per key, and uniform digests of uniform
answers. -/
theorem prEvent_exists_fresh_digestClash_le (oa : OracleComp (ofFn R) α) (n : ℕ)
    (hn : IsTotalQueryBound oa n) (event : α → Prop) (digest : (t : D) → R t → Digest)
    (hdigest : ∀ t x, Pr{let u ← $ᵗ R t}[digest t u = x] ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹)
    (keyDigests : D → List Digest) (m : ℕ) (hkey : ∀ t, (keyDigests t).length ≤ m)
    (avoid : List Digest) (havoid : avoid.length ≤ 1)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ pre q post, tableQueryLog oa g = pre ++ q :: post ∧ q.1 ∉ pre.map Sigma.fst ∧
        DigestClash digest keyDigests avoid pre q.1 q.2) :
    Pr{let result ← (simulateQ randomOracle oa).run' ∅}[event result] ≤
      (m + 1) * n ^ 2 / (Fintype.card Digest : ℝ≥0∞) := by
  have h := prEvent_exists_fresh_bad_le oa n hn event (DigestClash digest keyDigests avoid)
    (((m + 1) * n : ℕ) * (Fintype.card Digest : ℝ≥0∞)⁻¹)
    (fun pre t hlen _ => (prEvent_digestClash_le digest hdigest keyDigests m hkey avoid pre t).trans
      (by
        gcongr
        calc avoid.length + (m + 1) * pre.length + m ≤ (m + 1) * (pre.length + 1) := by
              rw [Nat.mul_succ]
              omega
          _ ≤ (m + 1) * n := Nat.mul_le_mul_left _ hlen)) htrace
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, ← mul_assoc]
  push_cast
  ring

end OracleComp
