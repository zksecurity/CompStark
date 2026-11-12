/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Transcript.Duplex
public import ArkLib.Interaction.Oracle.Security.HashChainObserver
public import ArkLib.Interaction.Oracle.Security.StandardBcs

/-! Fixed-table correspondence on ArkLib's challenge-erased keys. Message encodings are
protocol data, not a hash-chain oracle. The observer also applies to `StandardBcs.compiledCoin`:
commitments are public encoded moves and Merkle authentication hints are not absorbed.

Injectivity refers to the pre-permutation encoding, never to a finite hash or duplex output.
Tags recover scalar/nonce items inside a rate block. Message boundaries additionally require
prefix-free observer encodings (fixed-width scalar and digest moves satisfy this). An arbitrary
variable-length scalar list is not prefix-free. The raw statement remains part of the key;
seeding it with a digest makes no assertion of collision-free statement hashing. -/

namespace CompStark.Keccak.Transcript
open CompStark.BinaryFields CompStark.Keccak.Commit
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration
@[expose] public section

/-- Wire observations of public moves/commitments and challenge decoders. A grinding move's
encoding includes its tagged nonce and discarded squeeze; its check belongs to acceptance. -/
@[reducible] def Observer : {protocol : Protocol} → PublicCoin protocol → Type :=
  PublicCoin.rec (motive := fun _ _ ↦ Type) PUnit
    (fun {Moves} _ _ _ next ↦ (Moves → List Event) × ((move : Moves) → next move))
    (fun {Messages} _ _ _ _ next ↦ (Messages → List Event) × next)
    (fun {Challenge} _ _ _ next ↦ (E → Challenge) × next)

/-- Every authored move is self-delimiting in the event stream. The target squeeze is not
encoded; each strict ancestor challenge contributes one explicit squeeze event. -/
def Observer.PrefixFree : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Observer coin → Prop
  | _, .done, _ => True
  | _, @PublicCoin.sender _ _ _ next, obs =>
      HashChain.PrefixFree obs.1 ∧ ∀ move, Observer.PrefixFree (next move) (obs.2 move)
  | _, @PublicCoin.oracle _ _ _ _ next, obs =>
      HashChain.PrefixFree obs.1 ∧ Observer.PrefixFree next obs.2
  | _, @PublicCoin.challenge _ _ _ next, obs => Observer.PrefixFree next obs.2

/-- Encode an erased prefix, retaining every prior permutation boundary, including empty draws. -/
def Observer.encodeFrom : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Observer coin → Prefix PUnit coin → List Event
  | _, .done, _, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, obs, pre =>
      obs.1 pre.1 ++ Observer.encodeFrom (next pre.1) (obs.2 pre.1) pre.2
  | _, @PublicCoin.oracle _ _ _ _ next, obs, pre =>
      obs.1 pre.1 ++ Observer.encodeFrom next obs.2 pre.2
  | _, @PublicCoin.challenge _ _ _ next, obs, pre =>
      match pre with
      | .inl _ => []
      | .inr (_, pre) => .squeeze :: Observer.encodeFrom next obs.2 pre

/-- Read the decoder at the target challenge node without retaining ancestor answers. -/
def Observer.decode : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Observer coin → (pre : Prefix PUnit coin) → E → pre.Challenge
  | _, .done, _, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, obs, pre =>
      Observer.decode (next pre.1) (obs.2 pre.1) pre.2
  | _, @PublicCoin.oracle _ _ _ _ next, obs, pre => Observer.decode next obs.2 pre.2
  | _, @PublicCoin.challenge _ _ _ next, obs, pre =>
      match pre with
      | .inl _ => obs.1
      | .inr (_, pre) => Observer.decode next obs.2 pre

/-- Statement plus all prior events is the uncompressed key encoding. -/
def Observer.encode {Input : Type} {protocol : Input → Protocol}
    {coin : (input : Input) → PublicCoin (protocol input)}
    (obs : (input : Input) → Observer (coin input)) (key : Key Input PUnit coin) :
    Input × List Event := (key.1, Observer.encodeFrom (coin key.1) (obs key.1) key.2)

/-- Prefix-free observations recover a challenge-erased prefix from its event list. -/
theorem Observer.encodeFrom_injective : {protocol : Protocol} →
    (coin : PublicCoin protocol) → (obs : Observer coin) →
    Observer.PrefixFree coin obs → Function.Injective (Observer.encodeFrom coin obs)
  | _, .done, _, _, pre, _, _ => nomatch pre
  | _, @PublicCoin.sender Moves _ _ next, obs, framing, ⟨a, pre⟩, ⟨b, pre'⟩, h => by
      obtain ⟨rfl, rest⟩ := framing.1 a b _ _ h
      have same := Observer.encodeFrom_injective (next a) (obs.2 a) (framing.2 a) rest
      cases same
      rfl
  | _, @PublicCoin.oracle _ _ _ _ next, obs, framing, ⟨a, pre⟩, ⟨b, pre'⟩, h => by
      obtain ⟨rfl, rest⟩ := framing.1 a b _ _ h
      have same := Observer.encodeFrom_injective next obs.2 framing.2 rest
      cases same
      rfl
  | _, @PublicCoin.challenge _ _ _ next, obs, framing, pre, pre', h => by
      rcases pre with ⟨⟩ | ⟨⟨⟩, pre⟩ <;> rcases pre' with ⟨⟩ | ⟨⟨⟩, pre'⟩
      · rfl
      · cases h
      · cases h
      · have same := Observer.encodeFrom_injective next obs.2 framing (List.cons.inj h).2
        cases same
        rfl

/-- Prefix-free message encodings and explicit ancestor squeezes recover the whole erased key.
The per-round CI assumptions concern `challengeTable`: distinct keys sharing a sponge input would share a challenge and make CI false for that pair. -/
theorem Observer.encode_injective {Input : Type} {protocol : Input → Protocol}
    {coin : (input : Input) → PublicCoin (protocol input)}
    (obs : (input : Input) → Observer (coin input))
    (framing : ∀ input, Observer.PrefixFree (coin input) (obs input)) :
    Function.Injective (Observer.encode obs) := by
  rintro ⟨input, pre⟩ ⟨input', pre'⟩ h
  obtain ⟨rfl, h⟩ := Prod.mk.inj h
  have same := Observer.encodeFrom_injective (coin input) (obs input) (framing input) h
  cases same
  rfl

/-- Fixed-width scalar moves use only scalar-domain items, with no squeeze between their limbs. -/
def scalarEvents {n : ℕ} (xs : Vector E n) : List Event :=
  xs.toList.map fun x ↦ .absorb (.scalar x)

/-- Fixed-width scalar encodings delimit protocol moves in both directions. -/
theorem scalarEvents_framing (n : ℕ) :
    HashChain.PrefixFree (scalarEvents (n := n)) ∧
      HashChain.SuffixFree (scalarEvents (n := n)) := by
  have injective : Function.Injective (scalarEvents (n := n)) := by
    intro a b h
    apply Vector.toList_inj.mp
    exact (List.map_injective_iff.mpr (fun _ _ h ↦ by cases h; rfl)) h
  have length (a b : Vector E n) : (scalarEvents a).length = (scalarEvents b).length := by
    simp only [scalarEvents, List.length_map, Vector.length_toList]
  exact ⟨HashChain.prefixFree_of_length injective length,
    HashChain.suffixFree_of_length injective length⟩

/-- A root is sent as two ordinary scalar-domain items. -/
def digestEvents (digest : Digest) : List Event :=
  (digestScalars digest).map fun x ↦ .absorb (.scalar x)

/-- Within a digest-typed move the two-scalar encoding is prefix- and suffix-free.
It has no domain separation from a two-scalar move; the protocol fixes which is expected. -/
theorem digestEvents_framing :
    HashChain.PrefixFree digestEvents ∧ HashChain.SuffixFree digestEvents := by
  have injective : Function.Injective digestEvents := by
    intro a b h
    apply digestScalars_injective
    exact (List.map_injective_iff.mpr (fun _ _ h ↦ by cases h; rfl)) h
  have length (a b : Digest) : (digestEvents a).length = (digestEvents b).length := by
    simp only [digestEvents, List.length_map, digestScalars, List.length_cons, List.length_nil]
  exact ⟨HashChain.prefixFree_of_length injective length,
    HashChain.suffixFree_of_length injective length⟩

/-- Nonce moves have a fixed tagged item and one discarded squeeze, hence delimit both ways. -/
theorem grindEvents_framing :
    HashChain.PrefixFree grindEvents ∧ HashChain.SuffixFree grindEvents := by
  have injective : Function.Injective grindEvents := by
    intro a b h
    cases h
    rfl
  have length (a b : E) : (grindEvents a).length = (grindEvents b).length := by rfl
  exact ⟨HashChain.prefixFree_of_length injective length,
    HashChain.suffixFree_of_length injective length⟩

/-- Concrete deterministic table: replay the statement and encoded erased prefix, then squeeze.
This definition requires determinism; framing supplies the stronger key-binding property. -/
def challengeTable {Input : Type} {protocol : Input → Protocol}
    {coin : (input : Input) → PublicCoin (protocol input)}
    (initial : Input → State) (obs : (input : Input) → Observer (coin input)) :
    Table Input PUnit coin := fun key ↦
  Observer.decode (coin key.1) (obs key.1) key.2
    (squeeze (replay (initial key.1) (Observer.encode obs key).2)).1

/-- Replay the erased prover messages using exactly the observer's wire events, deriving challenges. -/
def Observer.execute : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Observer coin → State → Messages PUnit coin → protocol.tree.ExecutionPath
  | _, .done, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, obs, s, messages =>
      ⟨messages.1, Observer.execute (next messages.1) (obs.2 messages.1)
        (replay s (obs.1 messages.1)) messages.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, obs, s, messages =>
      ⟨messages.1, Observer.execute next obs.2 (replay s (obs.1 messages.1)) messages.2⟩
  | _, @PublicCoin.challenge _ _ _ next, obs, s, messages =>
      let draw := squeeze s
      ⟨obs.1 draw.1, Observer.execute next obs.2 draw.2 messages.2⟩

/-- Replaying concatenated event streams agrees with sequential replay. -/
theorem replay_append (s : State) (a b : List Event) :
    replay s (a ++ b) = replay (replay s a) b := List.foldl_append

/-- At any starting state, replay's challenges match the table of erased prefixes. -/
theorem Observer.execute_consistent : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (obs : Observer coin) → (s : State) → (messages : Messages PUnit coin) →
    CorrelationIntractable.Consistent coin
      (fun pre ↦ Observer.decode coin obs pre (squeeze (replay s (Observer.encodeFrom coin obs pre))).1)
      (Observer.execute coin obs s messages)
  | _, .done, _, _, _ => True.intro
  | _, @PublicCoin.sender _ _ _ next, obs, s, ⟨move, messages⟩ => by
      simp only [Observer.execute, CorrelationIntractable.Consistent,
        Observer.decode, Observer.encodeFrom, replay_append]
      exact Observer.execute_consistent (next move) (obs.2 move)
        (replay s (obs.1 move)) messages
  | _, @PublicCoin.oracle _ _ _ _ next, obs, s, messages => by
      simpa only [Observer.execute, CorrelationIntractable.Consistent,
        Observer.decode, Observer.encodeFrom, replay_append] using
        Observer.execute_consistent next obs.2 (replay s (obs.1 messages.1)) messages.2
  | _, @PublicCoin.challenge _ _ _ next, obs, s, messages => by
      constructor
      · rfl
      · exact Observer.execute_consistent next obs.2 (squeeze s).2 messages.2

/-- Actual duplex replay equals the challenge-erased fixed table at every challenge.
For the BCS pipeline take `coin := StandardBcs.compiledCoin Com iopCoin`; the verifier
must encode every transmitted move since the preceding squeeze, exactly once. -/
theorem duplex_consistent {Input : Type} {protocol : Input → Protocol}
    (coin : (input : Input) → PublicCoin (protocol input)) (initial : Input → State)
    (obs : (input : Input) → Observer (coin input)) (input : Input)
    (messages : Messages PUnit (coin input)) :
    CorrelationIntractable.Consistent (coin input)
      (Table.fibre (challengeTable initial obs) input)
      (Observer.execute (coin input) (obs input) (initial input) messages) := by
  exact Observer.execute_consistent (coin input) (obs input) (initial input) messages

/-- A successful grind exposes only its updated state to the subsequent protocol.
Its discarded challenge is checked independently and is absent from the public-coin tree. -/
theorem grind_acceptance (s : State) (bits : ℕ) (nonce : E)
    (accepted : (grindCheck s bits nonce).1 = true) :
    (bits = 0 → nonce = 0) ∧
      (bits ≠ 0 → lowBitsZero bits (squeeze (absorb s (.nonce nonce))).1 = true) := by
  constructor
  · intro h
    simpa only [grindCheck, h, ↓reduceIte, decide_eq_true_eq] using accepted
  · intro h
    simpa only [grindCheck, h, ↓reduceIte] using accepted

/-- Permutation cost of testing one nonce: a full pending block first flushes, then the
independent grinding test squeezes. Failed attempts start from the same unmodified state. -/
def grindAttemptCost (s : State) : ℕ := if s.pending.length = 4 then 2 else 1

/-- Resource accounting for a CI key producer with grinding. `base` includes seed, automatic
full-block flushes, protocol draws and accepted grinding checks; `attempts` counts extra failed
candidate tests at each grinding site. CI escape terms remain indexed by protocol challenges,
while these costs belong to each producer's Keccak/permutation budget. The subsequent
`StandardBcs.ciRel` assumption must cover that producer with its adaptive nonce search:
the key contains the accepted nonce and discarded squeeze through `grindEvents`.
There is no automatic
`2^-bits` security multiplier for fixed Keccak. -/
def ciPermutationBudget (base : ℕ) (attempts : List (State × ℕ)) : ℕ :=
  base + (attempts.map fun (s, count) ↦ count * grindAttemptCost s).sum

end
end CompStark.Keccak.Transcript
