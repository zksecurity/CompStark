/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.RandomOracle
public import CompStark.NonInteractiveError
public import CompStark.Ni.RoundBounds
public import ArkLib.Interaction.Oracle.Security.HashChain

/-! # Plonky3's duplex challenger is a hash chain

The verifier's duplex oracle (`RandomOracle.Query.duplex`) is a chain oracle in the sense of
ArkLib's `HashChain`: the state is the capacity, the input is the list of elements observed
since the last squeeze, and the output is the squeeze's `K` samples. The challenger
(`RandomOracle.withAnswers`) starts at the zero capacity and queries each squeeze at the
capacity the previous squeeze answered (`sample_cap`, `sample_key`): its capacity after the
squeezes of the blocks `bs` is `capOf answer bs`.

* `merkleSpec`, `translate`: the verifier's other oracles, the leaf hash and the compression, are
  the extra oracles next to the chain; `translate` reads every query of `spec F K` as a chain
  query or a Merkle hash, and the random oracle on `spec F K` is the random oracle on the two
  (`map_run_randomOracle`).
* `prEvent_le_prefix`: an event of a program against the verifier's oracles, making at most `Q`
  duplex calls, is at most the same event of the program against a random oracle keyed by the
  whole prefix of absorbed inputs, by ArkLib's simulator, plus `HashChain.chainError` of the
  capacities, `Q (Q + 1) / 2 / |F|⁸`.
* `chainError_mul_le_hashError`: that error, `2 + 2 ^ h` times over, is at most
  `hashError F h Q = (2 + 2 ^ h) Q² / |F|⁸`: `hashError` charges a fresh answer up to `2 + 2 ^ h`
  known digests per earlier query, and the chain's collisions and predictions need one.
-/

@[expose] public section
namespace CompStark.Fs
open CompStark.Stark CompStark.Iop CompStark.RandomOracle OracleSpec OracleComp
open Interaction.Oracle.Security
open scoped ENNReal

variable {F : Type} {K : Nat}

/-! ### The challenger's capacities -/

/-- The capacity after squeezing the blocks `bs`, latest first, on the duplex answers
`answer`: the zero capacity for none, the capacity answered at the latest squeeze otherwise. -/
def capOf [Zero F] (answer : (q : Query F) → Answer K q) : List (List F) → Digest F
  | [] => initCap
  | b :: bs => (answer (.duplex (capOf answer bs) b)).1

/-- Observing an element keeps the capacity. -/
theorem observe_cap [Zero F] (answer : (q : Query F) → Answer K q) (s : Sponge F) (x : F) :
    ((idealOf answer).observe s x).cap = s.cap := rfl

/-- A sample with no samples left squeezes: it queries the duplex oracle at the capacity and the
pending input, and takes the answer's capacity. -/
theorem sample_of_samples_eq_nil [Zero F] (answer : (q : Query F) → Answer K q) {s : Sponge F}
    (hs : s.samples = []) : (idealOf answer).sample s =
      ((answer (.duplex s.cap s.input)).2.toList.headD 0,
        ⟨(answer (.duplex s.cap s.input)).1, [],
          (answer (.duplex s.cap s.input)).2.toList.tail⟩) := by
  obtain ⟨cap, input, samples⟩ := s
  subst hs
  rfl

/-- A sample with samples left keeps the capacity. -/
theorem sample_of_samples_eq_cons [Zero F] (answer : (q : Query F) → Answer K q) {s : Sponge F}
    {x : F} {rest : List F} (hs : s.samples = x :: rest) :
    (idealOf answer).sample s = (x, ⟨s.cap, s.input, rest⟩) := by
  obtain ⟨cap, input, samples⟩ := s
  subst hs
  rfl

/-- **The challenger is a hash chain.** At the capacity of the blocks `bs`, a squeeze queries the
duplex oracle at the chain key of the prefix `s.input :: bs`, the capacity of `bs` and the pending
input, and moves to the capacity of `s.input :: bs`; a sample without a squeeze keeps the
capacity. -/
theorem sample_cap [Zero F] (answer : (q : Query F) → Answer K q) {s : Sponge F}
    {bs : List (List F)} (hcap : s.cap = capOf answer bs) :
    ((idealOf answer).sample s).2.cap =
      capOf answer (if s.samples = [] then s.input :: bs else bs) := by
  cases hs : s.samples with
  | nil =>
    rw [sample_of_samples_eq_nil answer hs]
    simp only [ite_true, capOf]
    rw [hcap]
  | cons x rest =>
    rw [sample_of_samples_eq_cons answer hs]
    simp only [reduceCtorEq, ite_false, hcap]

/-- A squeeze at the capacity of the blocks `bs` queries the duplex oracle at that capacity and
the pending input. -/
theorem sample_key [Zero F] (answer : (q : Query F) → Answer K q) {s : Sponge F}
    {bs : List (List F)} (hcap : s.cap = capOf answer bs) (hs : s.samples = []) :
    (idealOf answer).sample s =
      ((answer (.duplex (capOf answer bs) s.input)).2.toList.headD 0,
        ⟨capOf answer (s.input :: bs), [],
          (answer (.duplex (capOf answer bs) s.input)).2.toList.tail⟩) := by
  rw [sample_of_samples_eq_nil answer hs, hcap, capOf]

/-! ### The verifier's oracles as a chain and Merkle hashes -/

/-- The duplex oracle as a chain oracle: the capacity is the state, the elements observed since
the last squeeze are the input, and the squeeze's samples the output. -/
abbrev duplexSpec (F : Type) (K : Nat) : OracleSpec (Digest F × List F) :=
  HashChain.chainSpec (Digest F) (List F) (Vector F K)

/-- The Merkle hashes: a row's leaf hash, and the compression of two digests. -/
abbrev merkleSpec (F : Type) : OracleSpec (List F ⊕ (Digest F × Digest F)) :=
  (List F ⊕ (Digest F × Digest F)) →ₒ Digest F

/-- The duplex calls and the Merkle hashes. -/
abbrev sumSpec (F : Type) (K : Nat) := duplexSpec F K + merkleSpec F

/-- The verifier's oracle calls as chain queries and Merkle hashes. -/
def translate : QueryImpl (spec F K) (OracleComp (unifSpec + sumSpec F K))
  | .duplex cap input => liftM ((unifSpec + sumSpec F K).query (.inr (.inl (cap, input))))
  | .leaf row => liftM ((unifSpec + sumSpec F K).query (.inr (.inr (.inl row))))
  | .node left right => liftM ((unifSpec + sumSpec F K).query (.inr (.inr (.inr (left, right)))))

/-- A cache of the verifier's oracles as a cache of the chain and the Merkle hashes. -/
def cacheOf (c : (spec F K).QueryCache) : (sumSpec F K).QueryCache :=
  QueryCache.ofFn fun t => match t with
    | .inl (cap, input) => c (.duplex cap input)
    | .inr (.inl row) => c (.leaf row)
    | .inr (.inr (left, right)) => c (.node left right)

/-- Whether a call is a duplex call. -/
def isDuplex : Query F → Bool
  | .duplex .. => true
  | _ => false

variable [BaseField F]

theorem cacheOf_cacheQuery_duplex (c : (spec F K).QueryCache) (cap : Digest F) (input : List F)
    (u : Digest F × Vector F K) :
    cacheOf (c.cacheQuery (.duplex cap input) u) =
      (cacheOf c).cacheQuery (.inl (cap, input)) u := by
  refine QueryCache.ext fun t => ?_
  rcases t with ⟨cap', input'⟩ | row | ⟨left, right⟩
  · by_cases h : (cap', input') = (cap, input)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp [cacheOf]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
      simp only [cacheOf, QueryCache.ofFn_apply]
      rw [QueryCache.cacheQuery_of_ne _ _ (by intro h'; cases h'; exact h rfl)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    simp only [cacheOf, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    simp only [cacheOf, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]

theorem cacheOf_cacheQuery_leaf (c : (spec F K).QueryCache) (row : List F) (u : Digest F) :
    cacheOf (c.cacheQuery (.leaf row) u) = (cacheOf c).cacheQuery (.inr (.inl row)) u := by
  refine QueryCache.ext fun t => ?_
  rcases t with ⟨cap', input'⟩ | row' | ⟨left, right⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    simp only [cacheOf, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
  · by_cases h : row' = row
    · subst h
      simp [cacheOf]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
      simp only [cacheOf, QueryCache.ofFn_apply]
      rw [QueryCache.cacheQuery_of_ne _ _ (by intro h'; cases h'; exact h rfl)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    simp only [cacheOf, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]

theorem cacheOf_cacheQuery_node (c : (spec F K).QueryCache) (left right : Digest F)
    (u : Digest F) :
    cacheOf (c.cacheQuery (.node left right) u) =
      (cacheOf c).cacheQuery (.inr (.inr (left, right))) u := by
  refine QueryCache.ext fun t => ?_
  rcases t with ⟨cap', input'⟩ | row' | ⟨left', right'⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    simp only [cacheOf, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    simp only [cacheOf, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
  · by_cases h : (left', right') = (left, right)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp [cacheOf]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
      simp only [cacheOf, QueryCache.ofFn_apply]
      rw [QueryCache.cacheQuery_of_ne _ _ (by intro h'; cases h'; exact h rfl)]

omit [BaseField F] in
@[simp] theorem cacheOf_empty : cacheOf (∅ : (spec F K).QueryCache) = ∅ := by
  refine QueryCache.ext fun t => ?_
  rcases t with ⟨cap, input⟩ | row | ⟨left, right⟩ <;> rfl

theorem step_duplex (cap : Digest F) (input : List F) (c : (spec F K).QueryCache) :
    (fun z => (z.1, cacheOf z.2)) <$> ((spec F K).randomOracle (.duplex cap input)).run c =
      ((sumSpec F K).romImpl (.inr (.inl (cap, input)))).run (cacheOf c) := by
  rw [romImpl_apply_inr, randomOracle.run_eq, randomOracle.run_eq]
  have hc : (cacheOf c) (.inl (cap, input)) = c (.duplex cap input) := rfl
  rw [hc]
  cases h : c (.duplex cap input) with
  | some u => simp
  | none =>
    simp only [map_bind, map_pure, cacheOf_cacheQuery_duplex]
    rfl

theorem step_leaf (row : List F) (c : (spec F K).QueryCache) :
    (fun z => (z.1, cacheOf z.2)) <$> ((spec F K).randomOracle (.leaf row)).run c =
      ((sumSpec F K).romImpl (.inr (.inr (.inl row)))).run (cacheOf c) := by
  rw [romImpl_apply_inr, randomOracle.run_eq, randomOracle.run_eq]
  have hc : (cacheOf c) (.inr (.inl row)) = c (.leaf row) := rfl
  rw [hc]
  cases h : c (.leaf row) with
  | some u => simp
  | none =>
    simp only [map_bind, map_pure, cacheOf_cacheQuery_leaf]
    rfl

theorem step_node (left right : Digest F) (c : (spec F K).QueryCache) :
    (fun z => (z.1, cacheOf z.2)) <$> ((spec F K).randomOracle (.node left right)).run c =
      ((sumSpec F K).romImpl (.inr (.inr (.inr (left, right))))).run (cacheOf c) := by
  rw [romImpl_apply_inr, randomOracle.run_eq, randomOracle.run_eq]
  have hc : (cacheOf c) (.inr (.inr (left, right))) = c (.node left right) := rfl
  rw [hc]
  cases h : c (.node left right) with
  | some u => simp
  | none =>
    simp only [map_bind, map_pure, cacheOf_cacheQuery_node]
    rfl

/-- The random oracle on the verifier's oracles is the random oracle on the chain and the Merkle
hashes, through `translate`, with the caches matched by `cacheOf`. -/
theorem map_run_randomOracle {α : Type} (A : OracleComp (spec F K) α) (c : (spec F K).QueryCache) :
    (fun z => (z.1, cacheOf z.2)) <$> (simulateQ (spec F K).randomOracle A).run c =
      (simulateQ (sumSpec F K).romImpl (simulateQ translate A)).run (cacheOf c) := by
  induction A using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases q with ⟨cap, input⟩ | row | ⟨left, right⟩
    · rw [show simulateQ (sumSpec F K).romImpl (translate (.duplex cap input)) =
          (sumSpec F K).romImpl (.inr (.inl (cap, input))) by simp [translate],
        ← step_duplex, bind_map_left]
      simp only [ih]
    · rw [show simulateQ (sumSpec F K).romImpl (translate (.leaf row)) =
          (sumSpec F K).romImpl (.inr (.inr (.inl row))) by simp [translate],
        ← step_leaf, bind_map_left]
      simp only [ih]
    · rw [show simulateQ (sumSpec F K).romImpl (translate (.node left right)) =
          (sumSpec F K).romImpl (.inr (.inr (.inr (left, right)))) by simp [translate],
        ← step_node, bind_map_left]
      simp only [ih]

omit [BaseField F] in
/-- A program making at most `Q` duplex calls makes at most `Q` chain queries through
`translate`. -/
theorem isQueryBoundP_translate {α : Type} {A : OracleComp (spec F K) α} {Q : ℕ}
    (hQ : IsQueryBoundP A (fun q => isDuplex q = true) Q) :
    IsQueryBoundP (simulateQ translate A) (fun t => HashChain.isChain t = true) Q := by
  refine hQ.simulateQ_of_step (fun q hq => ?_) (fun q hq => ?_)
  · rcases q with ⟨cap, input⟩ | row | ⟨left, right⟩
    · simp only [translate]
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    · cases hq
    · cases hq
  · rcases q with ⟨cap, input⟩ | row | ⟨left, right⟩
    · exact absurd rfl hq
    · simp only [translate]
      rw [isQueryBoundP_query_iff]
      simp [HashChain.isChain]
    · simp only [translate]
      rw [isQueryBoundP_query_iff]
      simp [HashChain.isChain]

/-! ### The verifier's oracles and a prefix-keyed random oracle -/

/-- **Plonky3's duplex is a prefix-keyed random oracle until a capacity collision.** An event of
a program against the verifier's random oracles, making at most `Q` duplex calls, is at most the
same event of the program run against a random oracle keyed by the prefix of absorbed inputs
(ArkLib's simulator, starting at the zero capacity) and the Merkle hashes, plus the
collision-or-prediction error of `Q` capacities. -/
theorem prEvent_le_prefix {α : Type} (A : OracleComp (spec F K) α) {Q : ℕ}
    (hQ : IsQueryBoundP A (fun q => isDuplex q = true) Q) (E : α → Prop) :
    Pr{let a ← (simulateQ (spec F K).randomOracle A).run' ∅}[E a] ≤
      Pr{let a ← (simulateQ (HashChain.prefixSpec (Digest F) (List F) (Vector F K) +
          merkleSpec F).romImpl (HashChain.simulate initCap (simulateQ translate A))).run' ∅}[E a] +
        HashChain.chainError (Digest F) Q := by
  have hrun : (simulateQ (spec F K).randomOracle A).run' ∅ =
      (simulateQ (sumSpec F K).romImpl (simulateQ translate A)).run' ∅ := by
    have h := map_run_randomOracle A ∅
    rw [cacheOf_empty] at h
    change Prod.fst <$> (simulateQ (spec F K).randomOracle A).run ∅ =
      Prod.fst <$> (simulateQ (sumSpec F K).romImpl (simulateQ translate A)).run ∅
    rw [← h, Functor.map_map]
  rw [hrun]
  exact HashChain.prEvent_chain_le initCap _ (isQueryBoundP_translate hQ) E

/-- The collision-or-prediction error of `q` capacities is a `2 + 2 ^ h`-th of `hashError F h q`,
the share of one digest per query among the `2 + 2 ^ h` that `hashError` charges. -/
theorem chainError_mul_le_hashError (h q : Nat) :
    (2 + 2 ^ h) * HashChain.chainError (Digest F) q ≤ hashError F h q := by
  refine (mul_le_mul_right (HashChain.chainError_le _ q) _).trans (le_of_eq ?_)
  rw [hashError, Nat.card_eq_fintype_card (α := Digest F), Ni.card_digest, mul_div_assoc]
  push_cast
  rfl

end CompStark.Fs
