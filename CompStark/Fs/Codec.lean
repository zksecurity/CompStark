/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.Interaction.Oracle.Security.HashChainSqueeze

/-! # The inputs a duplex challenger absorbs along a transcript

A Fiat–Shamir verifier on a duplex challenger observes each prover move as a list of elements,
and squeezes at each challenge. An `Observer` of a public-coin protocol with draws `dec` records
how: the elements each public move, oracle message and draw witness is observed as, and the number
of squeezes at each challenge. The elements observed since the last squeeze are the input of the
next squeeze; a challenge squeezed `n` times squeezes `n - 1` more times with the empty input, and
a challenge squeezed `0` times leaves its observations to the next squeeze.

`Observer.encode` reads a restoration key of the decoded presentation, at a challenge node, as the
input of its first squeeze and the inputs of the squeezes before it, latest first: the chain inputs
a hash chain absorbs for the key's coins. The statement's elements (`tail`) are observed last
before the first squeeze, ahead of that squeeze's draw witness. When every observation is
prefix-free and every draw witness also suffix-free (`Observer.PrefixFree`) and the statement's
elements are injective, two keys that squeeze have equal inputs only if they are equal
(`Observer.encode_injective`): the inputs, oldest first, parse back into the moves.
-/

@[expose] public section
namespace CompStark.Fs
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration

variable {F C : Type}

/-- How a duplex verifier observes a protocol with draws `dec`: the elements of each public move,
oracle message and draw witness, and the number of squeezes at each challenge. -/
@[reducible] def Observer (F : Type) {C : Type} {protocol : Protocol.{0}}
    (coin : PublicCoin protocol) : Decoder C coin → Type :=
  PublicCoin.rec (motive := fun _ coin => Decoder C coin → Type) (fun _ => PUnit)
    (fun {Moves} _ _ _ obs dec => (Moves → List F) × ((move : Moves) → obs move (dec move)))
    (fun {Messages} _ _ _ _ obs dec => (Messages → List F) × obs dec)
    (@fun _ _ _ _ obs dec => ℕ × (dec.1.Witness → List F) × obs dec.2) coin

/-- An observation is prefix-free: the observed elements of a move, followed by anything, tell
the move and the rest. -/
def PrefixFree {α : Type} (f : α → List F) : Prop :=
  ∀ a b (r r' : List F), f a ++ r = f b ++ r' → a = b ∧ r = r'

/-- An observation is suffix-free: the observed elements of a move, after anything, tell the move
and what came before. -/
def SuffixFree {α : Type} (f : α → List F) : Prop :=
  ∀ a b (r r' : List F), r ++ f a = r' ++ f b → a = b ∧ r = r'

/-- An injective observation whose outputs all have the same length is prefix-free. -/
theorem prefixFree_of_length {α : Type} {f : α → List F} (hf : Function.Injective f)
    (hlen : ∀ a b, (f a).length = (f b).length) : PrefixFree f := fun a b _ _ h => by
  obtain ⟨hab, hr⟩ := List.append_inj h (hlen a b)
  exact ⟨hf hab, hr⟩

/-- An injective observation whose outputs all have the same length is suffix-free. -/
theorem suffixFree_of_length {α : Type} {f : α → List F} (hf : Function.Injective f)
    (hlen : ∀ a b, (f a).length = (f b).length) : SuffixFree f := fun a b _ _ h => by
  obtain ⟨hr, hab⟩ := List.append_inj' h (hlen a b)
  exact ⟨hf hab, hr⟩

/-- Every observation of the observer is prefix-free, and every draw witness also suffix-free. -/
def Observer.PrefixFree : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Observer F coin dec → Prop
  | _, .done, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, obs =>
      Fs.PrefixFree obs.1 ∧ ∀ move, Observer.PrefixFree (next move) (dec move) (obs.2 move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, obs =>
      Fs.PrefixFree obs.1 ∧ Observer.PrefixFree next dec obs.2
  | _, @PublicCoin.challenge _ _ _ next, dec, obs =>
      Fs.PrefixFree obs.2.1 ∧ Fs.SuffixFree obs.2.1 ∧ Observer.PrefixFree next dec.2 obs.2.2

/-- The number of squeezes at each challenge node. -/
def Observer.squeezes : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Observer F coin dec → Prefix PUnit coin → ℕ
  | _, .done, _, _, node => nomatch node
  | _, @PublicCoin.sender Moves _ _ next, dec, obs, node => by
      obtain ⟨move, node⟩ := (node : (move : Moves) × Prefix PUnit (next move))
      exact Observer.squeezes (next move) (dec move) (obs.2 move) node
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, obs, node => by
      obtain ⟨_, node⟩ := (node : Messages × Prefix PUnit next)
      exact Observer.squeezes next dec obs.2 node
  | _, @PublicCoin.challenge _ _ _ next, dec, obs, node => by
      rcases (node : PUnit ⊕ (PUnit × Prefix PUnit next)) with _ | ⟨_, node⟩
      · exact obs.1
      · exact Observer.squeezes next dec.2 obs.2.2 node

/-- Every squeezing challenge has observations since the last squeeze: `filled` holds when some
observation since the last squeeze is not empty. -/
def Observer.Fills : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Observer F coin dec → Prop → Prop
  | _, .done, _, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, obs, filled =>
      ∀ move, Observer.Fills (next move) (dec move) (obs.2 move) (filled ∨ obs.1 move ≠ [])
  | _, @PublicCoin.oracle _ _ _ _ next, dec, obs, filled =>
      ∀ message, Observer.Fills next dec obs.2 (filled ∨ obs.1 message ≠ [])
  | _, @PublicCoin.challenge _ _ _ next, dec, obs, filled =>
      (obs.1 ≠ 0 → ∀ w, filled ∨ obs.2.1 w ≠ []) ∧
        ∀ w, Observer.Fills next dec.2 obs.2.2
          (if obs.1 = 0 then filled ∨ obs.2.1 w ≠ [] else False)

variable [SampleableType C]

/-- The chain inputs of a key of the decoded presentation, after the completed inputs `acc`
(latest first) and with `pending` observed since the last squeeze: the input of the key's first
squeeze, its pending observations, `tail` and its witness, and the inputs before it, latest
first. `tail` is observed at the first squeeze only, before its witness. -/
def Observer.encodeFrom : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Observer F coin dec → (pending tail : List F) →
    (acc : List (List F)) → Prefix PUnit (decoded C coin dec) → List F × List (List F)
  | _, .done, _, _, _, _, _, pre => nomatch pre
  | _, @PublicCoin.sender Moves _ _ next, dec, obs, pending, tail, acc, pre => by
      obtain ⟨move, pre⟩ :=
        (pre : (move : Moves) × Prefix PUnit (decoded C (next move) (dec move)))
      exact Observer.encodeFrom (next move) (dec move) (obs.2 move) (pending ++ obs.1 move) tail
        acc pre
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, obs, pending, tail, acc, pre => by
      obtain ⟨message, pre⟩ := (pre : Messages × Prefix PUnit (decoded C next dec))
      exact Observer.encodeFrom next dec obs.2 (pending ++ obs.1 message) tail acc pre
  | _, @PublicCoin.challenge _ _ _ next, dec, obs, pending, tail, acc, pre => by
      obtain ⟨w, pre⟩ :=
        (pre : (_ : dec.1.Witness) × (PUnit ⊕ (PUnit × Prefix PUnit (decoded C next dec.2))))
      rcases pre with _ | ⟨_, pre⟩
      · exact (pending ++ tail ++ obs.2.1 w, acc)
      · exact if obs.1 = 0 then
          Observer.encodeFrom next dec.2 obs.2.2 (pending ++ obs.2.1 w) tail acc pre
        else Observer.encodeFrom next dec.2 obs.2.2 [] []
          (List.replicate (obs.1 - 1) [] ++ (pending ++ tail ++ obs.2.1 w) :: acc) pre

/-- The chain inputs of a key: its first squeeze's input and the inputs before it, latest first,
the statement's elements `tail` observed at the first squeeze, before its witness. -/
def Observer.encode {Input : Type} {protocol : Protocol.{0}} {coin : PublicCoin protocol}
    {dec : Decoder C coin} (obs : Observer F coin dec) (tail : Input → List F)
    (key : Key Input PUnit fun _ => decoded C coin dec) : List F × List (List F) :=
  obs.encodeFrom coin dec [] (tail key.1) [] key.2

/-- The chain inputs of a key, oldest first, are the completed inputs `acc` followed by a block
that starts with the pending observations; the rest does not depend on `pending` or `acc`. -/
theorem Observer.encodeFrom_reverse : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (obs : Observer F coin dec) → (pending tail : List F) →
    (acc : List (List F)) → (pre : Prefix PUnit (decoded C coin dec)) →
    ∃ r rest, ((obs.encodeFrom coin dec pending tail acc pre).1 ::
        (obs.encodeFrom coin dec pending tail acc pre).2).reverse =
          acc.reverse ++ (pending ++ r) :: rest ∧
      ((obs.encodeFrom coin dec [] tail [] pre).1 ::
        (obs.encodeFrom coin dec [] tail [] pre).2).reverse = r :: rest
  | _, .done, _, _, _, _, _, pre => nomatch pre
  | _, @PublicCoin.sender Moves _ _ next, dec, obs, pending, tail, acc, pre => by
      obtain ⟨move, pre⟩ :=
        (pre : (move : Moves) × Prefix PUnit (decoded C (next move) (dec move)))
      obtain ⟨r, rest, h1, h2⟩ := Observer.encodeFrom_reverse (next move) (dec move)
        (obs.2 move) (pending ++ obs.1 move) tail acc pre
      obtain ⟨r', rest', h1', h2'⟩ := Observer.encodeFrom_reverse (next move) (dec move)
        (obs.2 move) (obs.1 move) tail [] pre
      rw [h2', List.cons.injEq] at h2
      obtain ⟨hr, hrest⟩ := h2
      subst r' rest'
      refine ⟨obs.1 move ++ r, rest, ?_, ?_⟩
      · simp only [List.append_assoc] at h1
        exact h1
      · simp only [List.reverse_nil, List.nil_append] at h1'
        exact h1'
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, obs, pending, tail, acc, pre => by
      obtain ⟨message, pre⟩ := (pre : Messages × Prefix PUnit (decoded C next dec))
      obtain ⟨r, rest, h1, h2⟩ := Observer.encodeFrom_reverse next dec obs.2
        (pending ++ obs.1 message) tail acc pre
      obtain ⟨r', rest', h1', h2'⟩ := Observer.encodeFrom_reverse next dec obs.2
        (obs.1 message) tail [] pre
      rw [h2', List.cons.injEq] at h2
      obtain ⟨hr, hrest⟩ := h2
      subst r' rest'
      refine ⟨obs.1 message ++ r, rest, ?_, ?_⟩
      · simp only [List.append_assoc] at h1
        exact h1
      · simp only [List.reverse_nil, List.nil_append] at h1'
        exact h1'
  | _, @PublicCoin.challenge _ _ _ next, dec, obs, pending, tail, acc, pre => by
      obtain ⟨w, pre⟩ :=
        (pre : (_ : dec.1.Witness) × (PUnit ⊕ (PUnit × Prefix PUnit (decoded C next dec.2))))
      rcases pre with _ | ⟨_, pre⟩
      · exact ⟨tail ++ obs.2.1 w, [], by simp only [Observer.encodeFrom, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.append_assoc, and_self]⟩
      · by_cases hk : obs.1 = 0
        · obtain ⟨r, rest, h1, h2⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2
            (pending ++ obs.2.1 w) tail acc pre
          obtain ⟨r', rest', h1', h2'⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2
            (obs.2.1 w) tail [] pre
          rw [h2', List.cons.injEq] at h2
          obtain ⟨hr, hrest⟩ := h2
          subst r' rest'
          refine ⟨obs.2.1 w ++ r, rest, ?_, ?_⟩
          · simp only [Observer.encodeFrom, hk, ↓reduceIte, List.append_assoc] at h1 ⊢
            exact h1
          · simp only [Observer.encodeFrom, hk, ↓reduceIte, List.reverse_nil,
              List.nil_append] at h1' ⊢
            exact h1'
        · obtain ⟨r, rest, h1, h2⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2 [] []
            (List.replicate (obs.1 - 1) [] ++ (pending ++ tail ++ obs.2.1 w) :: acc) pre
          obtain ⟨r', rest', h1', h2'⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2 [] []
            (List.replicate (obs.1 - 1) [] ++ [[] ++ tail ++ obs.2.1 w]) pre
          rw [h2', List.cons.injEq] at h2
          obtain ⟨hr, hrest⟩ := h2
          subst r' rest'
          refine ⟨tail ++ obs.2.1 w, List.replicate (obs.1 - 1) [] ++ r :: rest, ?_, ?_⟩
          · simp only [Observer.encodeFrom, hk, ↓reduceIte, List.reverse_append,
              List.reverse_cons, List.reverse_replicate, List.append_assoc, List.nil_append,
              List.cons_append] at h1 ⊢
            exact h1
          · simp only [Observer.encodeFrom, hk, ↓reduceIte, List.reverse_append,
              List.reverse_cons, List.reverse_replicate, List.nil_append, List.cons_append,
              List.reverse_nil] at h1' ⊢
            exact h1'

/-- Two keys that squeeze, with no pending observations and no completed inputs, have equal
chain inputs only if their nodes and their statement's elements are equal. -/
theorem Observer.encodeFrom_injective : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (obs : Observer F coin dec) →
    obs.PrefixFree coin dec → (tail tail' : List F) →
    (pre pre' : Prefix PUnit (decoded C coin dec)) →
    obs.squeezes coin dec (Prefix.undecode coin dec pre) ≠ 0 →
    obs.squeezes coin dec (Prefix.undecode coin dec pre') ≠ 0 →
    ((obs.encodeFrom coin dec [] tail [] pre).1 ::
        (obs.encodeFrom coin dec [] tail [] pre).2).reverse =
      ((obs.encodeFrom coin dec [] tail' [] pre').1 ::
        (obs.encodeFrom coin dec [] tail' [] pre').2).reverse →
    pre = pre' ∧ tail = tail'
  | _, .done, _, _, _, _, _, pre, _, _, _, _ => nomatch pre
  | _, @PublicCoin.sender Moves _ _ next, dec, obs, hobs, tail, tail', pre, pre', hkey, hkey',
      h => by
      obtain ⟨move, pre⟩ :=
        (pre : (move : Moves) × Prefix PUnit (decoded C (next move) (dec move)))
      obtain ⟨move', pre'⟩ :=
        (pre' : (move : Moves) × Prefix PUnit (decoded C (next move) (dec move)))
      obtain ⟨r, rest, h1, h2⟩ := Observer.encodeFrom_reverse (next move) (dec move)
        (obs.2 move) (obs.1 move) tail [] pre
      obtain ⟨r', rest', h1', h2'⟩ := Observer.encodeFrom_reverse (next move') (dec move')
        (obs.2 move') (obs.1 move') tail' [] pre'
      simp only [Observer.encodeFrom, List.nil_append] at h
      rw [h1, h1', List.reverse_nil, List.nil_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := hobs.1 move move' r r' h.1
      obtain ⟨rfl, rfl⟩ := Observer.encodeFrom_injective (next move) (dec move) (obs.2 move)
        (hobs.2 move) tail tail' pre pre' hkey hkey' (by rw [h2, h2', h.2])
      exact ⟨rfl, rfl⟩
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, obs, hobs, tail, tail', pre, pre', hkey,
      hkey', h => by
      obtain ⟨message, pre⟩ := (pre : Messages × Prefix PUnit (decoded C next dec))
      obtain ⟨message', pre'⟩ := (pre' : Messages × Prefix PUnit (decoded C next dec))
      obtain ⟨r, rest, h1, h2⟩ := Observer.encodeFrom_reverse next dec obs.2
        (obs.1 message) tail [] pre
      obtain ⟨r', rest', h1', h2'⟩ := Observer.encodeFrom_reverse next dec obs.2
        (obs.1 message') tail' [] pre'
      simp only [Observer.encodeFrom, List.nil_append] at h
      rw [h1, h1', List.reverse_nil, List.nil_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := hobs.1 message message' r r' h.1
      obtain ⟨rfl, rfl⟩ := Observer.encodeFrom_injective next dec obs.2 hobs.2 tail tail' pre
        pre' hkey hkey' (by rw [h2, h2', h.2])
      exact ⟨rfl, rfl⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, obs, hobs, tail, tail', pre, pre', hkey, hkey',
      h => by
      obtain ⟨w, pre⟩ :=
        (pre : (_ : dec.1.Witness) × (PUnit ⊕ (PUnit × Prefix PUnit (decoded C next dec.2))))
      obtain ⟨w', pre'⟩ :=
        (pre' : (_ : dec.1.Witness) × (PUnit ⊕ (PUnit × Prefix PUnit (decoded C next dec.2))))
      rcases pre with _ | ⟨_, pre⟩ <;> rcases pre' with _ | ⟨_, pre'⟩
      · simp only [Observer.encodeFrom, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons.injEq, and_true] at h
        obtain ⟨rfl, rfl⟩ := hobs.2.1 w w' tail tail' h
        exact ⟨rfl, rfl⟩
      · have hk : obs.1 ≠ 0 := hkey
        obtain ⟨r, rest, h1, -⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2 [] []
          (List.replicate (obs.1 - 1) [] ++ ([] ++ tail' ++ obs.2.1 w') :: []) pre'
        simp only [Observer.encodeFrom, hk, ↓reduceIte] at h
        rw [h1] at h
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.reverse_append,
          List.reverse_replicate, List.cons_append, List.cons.injEq, List.nil_eq,
          List.append_eq_nil_iff, reduceCtorEq, and_false] at h
      · have hk : obs.1 ≠ 0 := hkey'
        obtain ⟨r, rest, h1, -⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2 [] []
          (List.replicate (obs.1 - 1) [] ++ ([] ++ tail ++ obs.2.1 w) :: []) pre
        simp only [Observer.encodeFrom, hk, ↓reduceIte] at h
        rw [h1] at h
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.reverse_append,
          List.reverse_replicate, List.cons_append, List.cons.injEq,
          List.append_eq_nil_iff, reduceCtorEq, and_false] at h
      · by_cases hk : obs.1 = 0
        · obtain ⟨r, rest, h1, h2⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2
            (obs.2.1 w) tail [] pre
          obtain ⟨r', rest', h1', h2'⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2
            (obs.2.1 w') tail' [] pre'
          simp only [Observer.encodeFrom, hk, ↓reduceIte, List.nil_append] at h
          rw [h1, h1', List.reverse_nil, List.nil_append, List.nil_append,
            List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := hobs.1 w w' r r' h.1
          obtain ⟨rfl, rfl⟩ := Observer.encodeFrom_injective next dec.2 obs.2.2 hobs.2.2 tail
            tail' pre pre' hkey hkey' (by rw [h2, h2', h.2])
          exact ⟨rfl, rfl⟩
        · obtain ⟨r, rest, h1, h2⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2 [] []
            (List.replicate (obs.1 - 1) [] ++ ([] ++ tail ++ obs.2.1 w) :: []) pre
          obtain ⟨r', rest', h1', h2'⟩ := Observer.encodeFrom_reverse next dec.2 obs.2.2 [] []
            (List.replicate (obs.1 - 1) [] ++ ([] ++ tail' ++ obs.2.1 w') :: []) pre'
          simp only [Observer.encodeFrom, hk, ↓reduceIte] at h
          rw [h1, h1'] at h
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.reverse_append,
            List.reverse_replicate, List.cons_append, List.cons.injEq,
            List.append_cancel_left_eq] at h
          obtain ⟨rfl, rfl⟩ := hobs.2.1 w w' tail tail' h.1
          obtain ⟨rfl, -⟩ := Observer.encodeFrom_injective next dec.2 obs.2.2 hobs.2.2 [] [] pre
            pre' hkey hkey' (by rw [h2, h2', h.2.1, h.2.2])
          exact ⟨rfl, rfl⟩

/-- **The inputs tell the keys apart.** With prefix-free observations and injective statement
elements, two keys whose nodes squeeze have equal chain inputs only if they are equal. -/
theorem Observer.encode_injective {Input : Type} {protocol : Protocol.{0}}
    {coin : PublicCoin protocol} {dec : Decoder C coin} (obs : Observer F coin dec)
    (hobs : obs.PrefixFree coin dec) (tail : Input → List F) (htail : Function.Injective tail)
    (key key' : Key Input PUnit fun _ => decoded C coin dec)
    (hkey : obs.squeezes coin dec (Prefix.undecode coin dec key.2) ≠ 0)
    (hkey' : obs.squeezes coin dec (Prefix.undecode coin dec key'.2) ≠ 0)
    (h : obs.encode tail key = obs.encode tail key') : key = key' := by
  obtain ⟨z, pre⟩ := key
  obtain ⟨z', pre'⟩ := key'
  obtain ⟨rfl, htz⟩ := obs.encodeFrom_injective coin dec hobs (tail z) (tail z') pre pre' hkey
    hkey' (congrArg (fun res => (res.1 :: res.2).reverse) h)
  obtain rfl := htail htz
  rfl

/-- The input of a key's first squeeze is not empty when every squeezing challenge has
observations since the last squeeze, and `filled` holds only with pending observations. -/
theorem Observer.encodeFrom_fst_ne_nil : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (obs : Observer F coin dec) →
    (filled : Prop) → obs.Fills coin dec filled → (pending tail : List F) →
    (acc : List (List F)) → (pre : Prefix PUnit (decoded C coin dec)) →
    (filled → pending ≠ []) → obs.squeezes coin dec (Prefix.undecode coin dec pre) ≠ 0 →
    (obs.encodeFrom coin dec pending tail acc pre).1 ≠ []
  | _, .done, _, _, _, _, _, _, _, pre, _, _ => nomatch pre
  | _, @PublicCoin.sender Moves _ _ next, dec, obs, filled, hfills, pending, tail, acc, pre,
      hpending, hkey => by
      obtain ⟨move, pre⟩ :=
        (pre : (move : Moves) × Prefix PUnit (decoded C (next move) (dec move)))
      refine Observer.encodeFrom_fst_ne_nil (next move) (dec move) (obs.2 move) _ (hfills move)
        (pending ++ obs.1 move) tail acc pre ?_ hkey
      rintro (hf | hm) he
      · exact hpending hf (List.append_eq_nil_iff.1 he).1
      · exact hm (List.append_eq_nil_iff.1 he).2
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, obs, filled, hfills, pending, tail, acc, pre,
      hpending, hkey => by
      obtain ⟨message, pre⟩ := (pre : Messages × Prefix PUnit (decoded C next dec))
      refine Observer.encodeFrom_fst_ne_nil next dec obs.2 _ (hfills message)
        (pending ++ obs.1 message) tail acc pre ?_ hkey
      rintro (hf | hm) he
      · exact hpending hf (List.append_eq_nil_iff.1 he).1
      · exact hm (List.append_eq_nil_iff.1 he).2
  | _, @PublicCoin.challenge _ _ _ next, dec, obs, filled, hfills, pending, tail, acc, pre,
      hpending, hkey => by
      obtain ⟨w, pre⟩ :=
        (pre : (_ : dec.1.Witness) × (PUnit ⊕ (PUnit × Prefix PUnit (decoded C next dec.2))))
      rcases pre with _ | ⟨_, pre⟩
      · have hk : obs.1 ≠ 0 := hkey
        simp only [Observer.encodeFrom, ne_eq, List.append_eq_nil_iff, not_and]
        intro hp hw
        rcases hfills.1 hk w with hf | hm
        · exact hpending hf hp.1
        · exact hm hw
      · by_cases hk : obs.1 = 0
        · have := Observer.encodeFrom_fst_ne_nil next dec.2 obs.2.2 _ (hfills.2 w)
            (pending ++ obs.2.1 w) tail acc pre ?_ hkey
          · simpa only [Observer.encodeFrom, hk, ↓reduceIte] using this
          · simp only [hk, ↓reduceIte]
            rintro (hf | hm) he
            · exact hpending hf (List.append_eq_nil_iff.1 he).1
            · exact hm (List.append_eq_nil_iff.1 he).2
        · have := Observer.encodeFrom_fst_ne_nil next dec.2 obs.2.2 _ (hfills.2 w) [] []
            (List.replicate (obs.1 - 1) [] ++ (pending ++ tail ++ obs.2.1 w) :: acc) pre ?_ hkey
          · simpa only [Observer.encodeFrom, hk, ↓reduceIte] using this
          · simp only [hk, ↓reduceIte, false_implies]

/-- The first squeeze of a key that squeezes absorbs a nonempty input. -/
theorem Observer.encode_fst_ne_nil {Input : Type} {protocol : Protocol.{0}}
    {coin : PublicCoin protocol} {dec : Decoder C coin} (obs : Observer F coin dec)
    (hfills : obs.Fills coin dec False) (tail : Input → List F)
    (key : Key Input PUnit fun _ => decoded C coin dec)
    (hkey : obs.squeezes coin dec (Prefix.undecode coin dec key.2) ≠ 0) :
    (obs.encode tail key).1 ≠ [] :=
  obs.encodeFrom_fst_ne_nil coin dec False hfills [] (tail key.1) [] key.2 False.elim hkey

/-- A key's inputs before its first squeeze number at most `N m` beyond the completed inputs `acc`,
when its protocol has at most `N` challenges on every path, each squeezed at most `m` times. -/
theorem Observer.length_encodeFrom_le : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (obs : Observer F coin dec) →
    {N m : ℕ} → coin.ChallengesLE N → (∀ node, obs.squeezes coin dec node ≤ m) →
    (pending tail : List F) → (acc : List (List F)) → (pre : Prefix PUnit (decoded C coin dec)) →
    (obs.encodeFrom coin dec pending tail acc pre).2.length ≤ acc.length + N * m
  | _, .done, _, _, _, _, _, _, _, _, _, pre => nomatch pre
  | _, @PublicCoin.sender Moves _ _ next, dec, obs, _, _, hN, hm, pending, tail, acc, pre => by
      obtain ⟨move, pre⟩ :=
        (pre : (move : Moves) × Prefix PUnit (decoded C (next move) (dec move)))
      exact Observer.length_encodeFrom_le (next move) (dec move) (obs.2 move) (hN move)
        (fun node ↦ hm ⟨move, node⟩) (pending ++ obs.1 move) tail acc pre
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, obs, _, _, hN, hm, pending, tail, acc, pre => by
      obtain ⟨message, pre⟩ := (pre : Messages × Prefix PUnit (decoded C next dec))
      exact Observer.length_encodeFrom_le next dec obs.2 hN
        (fun node ↦ hm (message, node)) (pending ++ obs.1 message) tail acc pre
  | _, @PublicCoin.challenge _ _ _ next, dec, obs, N, m, hN, hm, pending, tail, acc, pre => by
      obtain ⟨w, pre⟩ :=
        (pre : (_ : dec.1.Witness) × (PUnit ⊕ (PUnit × Prefix PUnit (decoded C next dec.2))))
      have hk : obs.1 ≤ m := hm (Sum.inl PUnit.unit)
      have hm' : ∀ node, Observer.squeezes next dec.2 obs.2.2 node ≤ m :=
        fun node ↦ hm (Sum.inr (PUnit.unit, node))
      obtain ⟨hN0, hN⟩ := hN
      have hNm : (N - 1) * m + m = N * m := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hN0]
      rcases pre with _ | ⟨_, pre⟩
      · exact Nat.le_add_right _ _
      · by_cases hk0 : obs.1 = 0
        · have := Observer.length_encodeFrom_le next dec.2 obs.2.2 hN hm'
            (pending ++ obs.2.1 w) tail acc pre
          simp only [Observer.encodeFrom, hk0, ↓reduceIte]
          omega
        · have := Observer.length_encodeFrom_le next dec.2 obs.2.2 hN hm' [] []
            (List.replicate (obs.1 - 1) [] ++ (pending ++ tail ++ obs.2.1 w) :: acc) pre
          simp only [Observer.encodeFrom, hk0, ↓reduceIte]
          simp only [List.length_append, List.length_replicate, List.length_cons] at this
          omega

/-- A key's inputs before its first squeeze number at most `N m`, when its protocol has at most `N`
challenges on every path, each squeezed at most `m` times. -/
theorem Observer.length_encode_le {Input : Type} {protocol : Protocol.{0}}
    {coin : PublicCoin protocol} {dec : Decoder C coin} (obs : Observer F coin dec) {N m : ℕ}
    (hN : coin.ChallengesLE N) (hm : ∀ node, obs.squeezes coin dec node ≤ m)
    (tail : Input → List F) (key : Key Input PUnit fun _ => decoded C coin dec) :
    (obs.encode tail key).2.length ≤ N * m := by
  simpa only [Observer.encode, List.length_nil, Nat.zero_add] using
    obs.length_encodeFrom_le coin dec hN hm [] (tail key.1) [] key.2

end CompStark.Fs
