/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Protocol
public import CompStark.Keccak.Lanes

/-! Statement-seeded overwrite-duplex challenges for the compiled typed protocol. Unlike a
scalar-only observer, a grouped bus, OOD or query move records every squeeze it consumes. -/

set_option Elab.async false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section
namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Multilinear CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security
open StateRestoration


/-- Typed wire observations with a concrete multi-squeeze decoder at each verifier move. -/
@[reducible] def WireObserver : {protocol : Protocol} → PublicCoin protocol → Type :=
  PublicCoin.rec (motive := fun _ _ => Type) PUnit
    (fun {Moves} _ _ _ next => (Moves → List Transcript.Event) × ((move : Moves) → next move))
    (fun {Messages} _ _ _ _ next => (Messages → List Transcript.Event) × next)
    (fun {Challenge} _ _ _ next => Draw Challenge × next)

/-- Encoding of a challenge-erased prefix includes every earlier challenge's full squeeze block. -/
def WireObserver.encodeFrom : {protocol : Protocol} → (coin : PublicCoin protocol) →
    WireObserver coin → Prefix PUnit coin → List Transcript.Event
  | _, .done, _, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, observer, pre =>
      observer.1 pre.1 ++ encodeFrom (next pre.1) (observer.2 pre.1) pre.2
  | _, @PublicCoin.oracle _ _ _ _ next, observer, pre => observer.1 pre.1 ++ encodeFrom next observer.2 pre.2
  | _, @PublicCoin.challenge _ _ _ next, observer, pre =>
      match pre with
      | .inl _ => []
      | .inr (_, pre) => List.replicate observer.1.width .squeeze ++ encodeFrom next observer.2 pre

/-- Statement and uncompressed events form the pre-permutation key encoding. -/
def WireObserver.encode {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (observer : (statement : Statement) → WireObserver (coin statement))
    (key : Key Statement PUnit coin) : Statement × List Transcript.Event :=
  (key.1, WireObserver.encodeFrom (coin key.1) (observer key.1) key.2)

/-- Decode the typed challenge at the selected prefix from its replayed duplex state. -/
def WireObserver.decode : {protocol : Protocol} → (coin : PublicCoin protocol) →
    WireObserver coin → (pre : Prefix PUnit coin) → Transcript.State → pre.Challenge
  | _, .done, _, pre, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, observer, pre, state => decode (next pre.1) (observer.2 pre.1) pre.2 state
  | _, @PublicCoin.oracle _ _ _ _ next, observer, pre, state => decode next observer.2 pre.2 state
  | _, @PublicCoin.challenge _ _ _ next, observer, pre, state =>
      match pre with
      | .inl _ => (observer.1.run state).1
      | .inr (_, pre) => decode next observer.2 pre state

/-- Every compiled move is observed once; only Merkle roots, never authentication hints, are absorbed. -/
def Presentation.observer : {original : Protocol} → (presentation : Presentation original) →
    WireObserver (StandardBcs.compiledCoin Commit.Digest presentation.coin)
  | _, .refine wire _ => wire.observer
  | _, .done => PUnit.unit
  | _, @Presentation.sender _ _ _ encode next => ⟨encode, fun move => (next move).observer⟩
  | _, @Presentation.reveal _ _ _ _ encode next => ⟨encode, fun _ => next.observer⟩
  | _, @Presentation.merkle _ _ _ _ _ next => ⟨Transcript.digestEvents, fun _ => next.observer⟩
  | _, @Presentation.announce _ _ _ encode _ next => ⟨encode, fun move => (next move).observer⟩
  | _, .grind _ next => ⟨Transcript.grindEvents, fun _ => next.observer⟩
  | _, @Presentation.challenge _ _ _ _ _ _ _ draw next => ⟨draw, next.observer⟩

/-- Check every setup announcement and grinding move at its actual prefix state. A grinding
squeeze advances the transcript without contributing a verifier challenge rank. -/
def Presentation.grindingChecks : {original : Protocol} → (presentation : Presentation original) →
    (StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath → Transcript.State → Prop
  | _, .refine wire _, path, state => wire.grindingChecks path state
  | _, .done, _, _ => True
  | _, @Presentation.sender _ _ _ encode next, path, state =>
      (next path.1).grindingChecks path.2 (Transcript.replay state (encode path.1))
  | _, @Presentation.reveal _ _ _ _ encode next, path, state =>
      next.grindingChecks path.2 (Transcript.replay state (encode path.1))
  | _, @Presentation.merkle _ _ _ _ _ next, path, state =>
      next.grindingChecks path.2 (Transcript.replay state (Transcript.digestEvents path.1))
  | _, @Presentation.announce _ _ _ encode valid next, path, state =>
      valid path.1 ∧ (next path.1).grindingChecks path.2 (Transcript.replay state (encode path.1))
  | _, .grind bits next, path, state =>
      (Transcript.grindCheck state bits path.1).1 = true ∧
        next.grindingChecks path.2 (Transcript.grindCheck state bits path.1).2
  | _, @Presentation.challenge _ _ _ _ _ _ _ draw next, path, state => next.grindingChecks path.2 (draw.run state).2

/-- The grinding bits of the nonce immediately before the challenge a key ends at, if any. -/
def Presentation.keyGrind : {original : Protocol} → (presentation : Presentation original) →
    Prefix PUnit (StandardBcs.compiledCoin Commit.Digest presentation.coin) → Option ℕ → Option ℕ
  | _, .refine wire _, pre, before => wire.keyGrind pre before
  | _, .done, pre, _ => nomatch pre
  | _, @Presentation.sender _ _ _ _ next, pre, _ => (next pre.1).keyGrind pre.2 none
  | _, @Presentation.reveal _ _ _ _ _ next, pre, _ => next.keyGrind pre.2 none
  | _, @Presentation.merkle _ _ _ _ _ next, pre, _ => next.keyGrind pre.2 none
  | _, @Presentation.announce _ _ _ _ _ next, pre, _ => (next pre.1).keyGrind pre.2 none
  | _, .grind bits next, pre, _ => next.keyGrind pre.2 (some bits)
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, pre, before => match pre with
      | .inl _ => before
      | .inr pair => next.keyGrind pair.2 none

/-- The low seventeen bits of a grinding squeeze. -/
abbrev GrindProbe := Fin (2 ^ 17)

/-- The low seventeen bits of a squeeze's first limb, the window the verifier's grinding test reads. -/
def grindProbe (squeeze : E) : GrindProbe :=
  ⟨(Lanes.laneWord (squeeze.limb 0)).toNat % 2 ^ 17, Nat.mod_lt _ (Nat.two_pow_pos 17)⟩

/-- A passing grinding test has `bits` low zero bits in its probe. -/
theorem grindProbe_passes (state : Transcript.State) (bits : ℕ) (nonce : E)
    (passed : (Transcript.grindCheck state bits nonce).1 = true) :
    (grindProbe (Transcript.squeeze (Transcript.absorb state (.nonce nonce))).1).val % 2 ^ bits = 0 := by
  by_cases zero : bits = 0
  · subst zero
    exact Nat.mod_one _
  have low := of_decide_eq_true ((Transcript.grind_acceptance state bits nonce passed).2 zero)
  change (Lanes.laneWord _).toNat % 2 ^ 17 % 2 ^ bits = 0
  generalize (Lanes.laneWord ((Transcript.squeeze (Transcript.absorb state (.nonce nonce))).1.limb 0)).toNat = a
    at low ⊢
  by_cases small : bits ≤ 17
  · rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 small)]
    rwa [Nat.min_eq_left (by omega)] at low
  · have divides : 2 ^ 17 ∣ a := (Nat.pow_dvd_pow 2 (by omega : 17 ≤ min bits 64)).trans
      (Nat.dvd_of_mod_eq_zero low)
    rw [Nat.mod_eq_zero_of_dvd divides, Nat.zero_mod]

/-- The grinding probe a key reads from a duplex state: the squeeze of the nonce immediately before the
challenge it ends at, replayed along the key's prefix as `grindingChecks` replays it. -/
def Presentation.keyProbe : {original : Protocol} → (presentation : Presentation original) →
    Prefix PUnit (StandardBcs.compiledCoin Commit.Digest presentation.coin) → Transcript.State →
      GrindProbe → GrindProbe
  | _, .refine wire _, pre, state, before => wire.keyProbe pre state before
  | _, .done, pre, _, _ => nomatch pre
  | _, @Presentation.sender _ _ _ encode next, pre, state, _ =>
      (next pre.1).keyProbe pre.2 (Transcript.replay state (encode pre.1)) 0
  | _, @Presentation.reveal _ _ _ _ encode next, pre, state, _ =>
      next.keyProbe pre.2 (Transcript.replay state (encode pre.1)) 0
  | _, @Presentation.merkle _ _ _ _ _ next, pre, state, _ =>
      next.keyProbe pre.2 (Transcript.replay state (Transcript.digestEvents pre.1)) 0
  | _, @Presentation.announce _ _ _ encode _ next, pre, state, _ =>
      (next pre.1).keyProbe pre.2 (Transcript.replay state (encode pre.1)) 0
  | _, .grind bits next, pre, state, _ =>
      next.keyProbe pre.2 (Transcript.grindCheck state bits pre.1).2
        (grindProbe (Transcript.squeeze (Transcript.absorb state (.nonce pre.1))).1)
  | _, @Presentation.challenge _ _ _ _ _ _ _ draw next, pre, state, before => match pre with
      | .inl _ => before
      | .inr pair => next.keyProbe pair.2 (draw.run state).2 0

/-- Along a path whose grinding checks pass, every key drawn after a grinding nonce of `bits` bits reads
a probe with `bits` low zero bits. -/
theorem Presentation.grindingChecks_keyProbe {original : Protocol} (presentation : Presentation original)
    (path : (StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath) (state : Transcript.State)
    (checks : presentation.grindingChecks path state) (before : Option ℕ) (probe : GrindProbe)
    (passes : ∀ bits, before = some bits → probe.val % 2 ^ bits = 0) :
    ∀ pre ∈ prefixKeys (StandardBcs.compiledCoin Commit.Digest presentation.coin)
        (CorrelationIntractable.erasePath _ path), ∀ bits,
      presentation.keyGrind pre before = some bits → (presentation.keyProbe pre state probe).val % 2 ^ bits = 0 := by
  induction presentation generalizing state before probe with
  | refine wire projection ih => exact ih path state checks before probe passes
  | done => intro pre member; exact nomatch pre
  | sender encode next ih =>
      intro pre member
      change pre ∈ (prefixKeys (StandardBcs.compiledCoin Commit.Digest (next path.1).coin)
        (CorrelationIntractable.erasePath _ path.2)).map (Sigma.mk path.1) at member
      obtain ⟨q, inner, rfl⟩ := List.mem_map.mp member
      exact ih path.1 path.2 _ checks none 0 nofun q inner
  | reveal encode next ih =>
      intro pre member
      change pre ∈ (prefixKeys (StandardBcs.compiledCoin Commit.Digest next.coin)
        (CorrelationIntractable.erasePath _ path.2)).map (Sigma.mk path.1) at member
      obtain ⟨q, inner, rfl⟩ := List.mem_map.mp member
      exact ih path.2 _ checks none 0 nofun q inner
  | merkle layout next ih =>
      intro pre member
      change pre ∈ (prefixKeys (StandardBcs.compiledCoin Commit.Digest next.coin)
        (CorrelationIntractable.erasePath _ path.2)).map (Sigma.mk path.1) at member
      obtain ⟨q, inner, rfl⟩ := List.mem_map.mp member
      exact ih path.2 _ checks none 0 nofun q inner
  | announce encode valid next ih =>
      intro pre member
      change pre ∈ (prefixKeys (StandardBcs.compiledCoin Commit.Digest (next path.1).coin)
        (CorrelationIntractable.erasePath _ path.2)).map (Sigma.mk path.1) at member
      obtain ⟨q, inner, rfl⟩ := List.mem_map.mp member
      exact ih path.1 path.2 _ checks.2 none 0 nofun q inner
  | grind bits next ih =>
      intro pre member
      change pre ∈ (prefixKeys (StandardBcs.compiledCoin Commit.Digest next.coin)
        (CorrelationIntractable.erasePath _ path.2)).map (Sigma.mk path.1) at member
      obtain ⟨q, inner, rfl⟩ := List.mem_map.mp member
      exact ih path.2 _ checks.2 (some bits) _
        (fun _ same => Option.some.inj same ▸ grindProbe_passes state bits path.1 checks.1) q inner
  | challenge move shape draw next ih =>
      intro pre member
      change pre ∈ .inl PUnit.unit :: (prefixKeys (StandardBcs.compiledCoin Commit.Digest next.coin)
        (CorrelationIntractable.erasePath _ path.2)).map (fun q => .inr ⟨PUnit.unit, q⟩) at member
      rcases List.mem_cons.mp member with rfl | member
      · exact passes
      · obtain ⟨q, inner, rfl⟩ := List.mem_map.mp member
        exact ih path.2 _ checks none 0 nofun q inner

/-- Actual replay derives the challenges in their typed blocks and consumes all their squeezes. -/
def WireObserver.execute : {protocol : Protocol} → (coin : PublicCoin protocol) →
    WireObserver coin → Transcript.State → Messages PUnit coin → protocol.tree.ExecutionPath
  | _, .done, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, observer, state, messages =>
      ⟨messages.1, execute (next messages.1) (observer.2 messages.1)
        (Transcript.replay state (observer.1 messages.1)) messages.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, observer, state, messages =>
      ⟨messages.1, execute next observer.2
        (Transcript.replay state (observer.1 messages.1)) messages.2⟩
  | _, @PublicCoin.challenge _ _ _ next, observer, state, messages =>
      let result := observer.1.run state
      ⟨result.1, execute next observer.2 result.2 messages.2⟩

/-- Replaying a block of squeeze events advances exactly the block runner's state. -/
theorem squeezeMany_state (count : ℕ) (state : Transcript.State) :
    (squeezeMany count state).2 =
      Transcript.replay state (List.replicate count Transcript.Event.squeeze) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      simpa only [squeezeMany, List.replicate_succ, Transcript.replay, List.foldl_cons] using ih (Transcript.squeeze state).2

/-- Any typed observer execution agrees with replay of every challenge-erased prefix. -/
theorem WireObserver.execute_consistent : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (observer : WireObserver coin) → (state : Transcript.State) →
    (messages : Messages PUnit coin) → CorrelationIntractable.Consistent coin
      (fun pre => decode coin observer pre (Transcript.replay state (encodeFrom coin observer pre)))
      (execute coin observer state messages)
  | _, .done, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, observer, state, ⟨move, messages⟩ => by
      simpa only [execute, CorrelationIntractable.Consistent, decode, encodeFrom,
        Transcript.replay_append] using execute_consistent (next move) (observer.2 move)
          (Transcript.replay state (observer.1 move)) messages
  | _, @PublicCoin.oracle _ _ _ _ next, observer, state, messages => by
      simpa only [execute, CorrelationIntractable.Consistent, decode, encodeFrom,
        Transcript.replay_append] using execute_consistent next observer.2
          (Transcript.replay state (observer.1 messages.1)) messages.2
  | _, @PublicCoin.challenge _ _ _ next, observer, state, messages => by
      constructor
      · rfl
      · change CorrelationIntractable.Consistent next
          (fun pre => decode next observer.2 pre (Transcript.replay state
            (List.replicate observer.1.width .squeeze ++ encodeFrom next observer.2 pre)))
          (execute next observer.2 (observer.1.run state).2 messages.2)
        simp only [Transcript.replay_append, ← squeezeMany_state]
        exact execute_consistent next observer.2 (observer.1.run state).2 messages.2

/-- Prefix-free message encodings and nonempty challenge blocks make erased keys recoverable. -/
def WireObserver.Framed : {protocol : Protocol} → (coin : PublicCoin protocol) →
    WireObserver coin → Prop
  | _, .done, _ => True
  | _, @PublicCoin.sender _ _ _ next, observer => HashChain.PrefixFree observer.1 ∧
      ∀ move, Framed (next move) (observer.2 move)
  | _, @PublicCoin.oracle _ _ _ _ next, observer => HashChain.PrefixFree observer.1 ∧ Framed next observer.2
  | _, @PublicCoin.challenge _ _ _ next, observer => 0 < observer.1.width ∧ Framed next observer.2

/-- Every encoded level asks at least one Merkle column query. -/
def positiveQueries : {n : ℕ} → Whir.Schedule K n → Prop
  | _, .last _ _ _ queries => 0 < queries
  | _, .more _ _ queries rest => 0 < queries ∧ positiveQueries rest

/-- Presentation framing records each public encoding and each positive draw width. -/
def Presentation.Framed : {original : Protocol} → Presentation original → Prop
  | _, .refine wire _ => wire.Framed
  | _, .done => True
  | _, @Presentation.sender _ _ _ encode next => HashChain.PrefixFree encode ∧ ∀ move, (next move).Framed
  | _, @Presentation.reveal _ _ _ _ encode next => HashChain.PrefixFree encode ∧ next.Framed
  | _, @Presentation.merkle _ _ _ _ _ next => next.Framed
  | _, @Presentation.announce _ _ _ encode _ next => HashChain.PrefixFree encode ∧ ∀ move, (next move).Framed
  | _, .grind _ next => next.Framed
  | _, @Presentation.challenge _ _ _ _ _ _ _ draw next => 0 < draw.width ∧ next.Framed

/-- Presentation framing implies framing of its compiled transcript observer. -/
theorem Presentation.Framed.observer {original : Protocol} (presentation : Presentation original)
    (framed : presentation.Framed) : WireObserver.Framed
      (StandardBcs.compiledCoin Commit.Digest presentation.coin) presentation.observer := by
  induction presentation with
  | refine wire projection ih => exact ih framed
  | done => trivial
  | sender encode next ih => exact ⟨framed.1, fun move => ih move (framed.2 move)⟩
  | reveal encode next ih => exact ⟨framed.1, fun _ => ih framed.2⟩
  | merkle layout next ih => exact ⟨Transcript.digestEvents_framing.1, fun _ => ih framed⟩
  | announce encode valid next ih => exact ⟨framed.1, fun move => ih move (framed.2 move)⟩
  | grind bits next ih => exact ⟨Transcript.grindEvents_framing.1, fun _ => ih framed⟩
  | challenge move shape draw next ih => exact ⟨framed.1, ih framed.2⟩

/-- Appending framed presentations preserves the event framing. -/
theorem Presentation.Framed.append {first second : Protocol} (presentation : Presentation first)
    (suffix : Presentation second) (head : presentation.Framed) (tail : suffix.Framed) :
    (presentation.append suffix).Framed := by
  induction presentation with
  | refine wire projection ih => exact ih head
  | done => exact tail
  | sender encode next ih => exact ⟨head.1, fun move => ih move (head.2 move)⟩
  | reveal encode next ih => exact ⟨head.1, ih head.2⟩
  | merkle layout next ih => exact ih head
  | announce encode valid next ih => exact ⟨head.1, fun move => ih move (head.2 move)⟩
  | grind bits next ih => exact ih head
  | challenge move shape draw next ih => exact ⟨head.1, ih head.2⟩

/-- Injective fixed-length field coordinates inherit scalar-event framing. -/
theorem fieldEvents_framed {Message : Type} {n : ℕ} (coordinates : Message → Fin n → E)
    (injective : Function.Injective coordinates) :
    HashChain.PrefixFree (fun message => fieldEvents (coordinates message)) := by
  intro a b rest rest' equal
  obtain ⟨same, rest⟩ := (Transcript.scalarEvents_framing n).1
    (Vector.ofFn (coordinates a)) (Vector.ofFn (coordinates b)) rest rest' equal
  refine ⟨injective ?_, rest⟩
  apply List.ofFn_injective
  simpa only [Vector.toList_ofFn] using congrArg Vector.toList same

/-- Boolean coordinates are enumerated by the low bits of the fixed-width indices. -/
theorem cubeEnumeration_surjective (n : ℕ) :
    Function.Surjective (fun i : Fin (2 ^ n) => fun bit : Fin n => i.val.testBit bit.val) := by
  intro row
  let bits := BitVec.ofBoolListLE (List.ofFn row)
  refine ⟨⟨bits.toNat, ?_⟩, ?_⟩
  · simpa only [bits, List.length_ofFn] using bits.isLt
  · funext bit
    simp only [BitVec.testBit_toNat, bits, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, bit.isLt, ↓reduceDIte,
      Option.getD_some, Fin.eta]

/-- The full plaintext table encoding retains each Boolean-coordinate value. -/
theorem plaintextEvents_framed (n : ℕ) : HashChain.PrefixFree
    (fun table : Whir.Table E n => fieldEvents fun i : Fin (2 ^ n) =>
      table (fun bit => i.val.testBit bit.val)) := by
  apply fieldEvents_framed
  intro a b equal
  funext row
  obtain ⟨i, rfl⟩ := cubeEnumeration_surjective n row
  exact congrFun equal i

/-- Flattening fixed-width dependent table rows retains their boundaries. -/
theorem dependentEvents_framed {n : ℕ} (width : Fin n → ℕ) : HashChain.PrefixFree
    (fun values : (i : Fin n) → Fin (width i) → E =>
      ((List.finRange n).flatMap fun i => List.ofFn (values i)).map
        (fun value => Transcript.Event.absorb (.scalar value))) := by
  induction n with
  | zero =>
      intro a b rest rest' equal
      exact ⟨Subsingleton.elim _ _, equal⟩
  | succ n ih =>
      intro a b rest rest' equal
      simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map,
        List.map_append] at equal
      have split := fieldEvents_framed (n := width 0) id Function.injective_id
      simp only [fieldEvents, Transcript.scalarEvents, Vector.toList_ofFn, id_eq] at split
      rw [List.append_assoc, List.append_assoc] at equal
      obtain ⟨head, equal⟩ := split (a 0) (b 0) _ _ equal
      obtain ⟨tail, equal⟩ := ih (fun i => width i.succ) (fun i => a i.succ)
        (fun i => b i.succ) rest rest' equal
      refine ⟨?_, equal⟩
      funext i
      exact Fin.cases head (fun j => congrFun tail j) i

/-- Scalar sumcheck messages and draws preserve framing of their suffix. -/
theorem whirRounds_framed {tail : Protocol} (suffix : Presentation tail) (h : suffix.Framed)
    (count : ℕ) : (whirRounds suffix count).Framed := by
  induction count with
  | zero => exact h
  | succ count ih =>
      refine ⟨fieldEvents_framed _ ?_, fun _ => ⟨by decide, ih⟩⟩
      intro a b equal
      apply Prod.ext (congrFun equal 0)
      funext i
      fin_cases i
      exact congrFun equal 1

/-- Positive queries in valid encoded dimensions consume a positive number of squeezes. -/
theorem queryDraw_positive (queries columns : ℕ) (positive : 0 < queries)
    (columns_pos : 0 < columns) (columns_le : columns ≤ 64) :
    0 < (queryDraw queries columns).width := by
  change 0 < (queries + 192 / columns - 1) / (192 / columns)
  have per : 0 < 192 / columns := Nat.div_pos (by omega) columns_pos
  apply Nat.div_pos _ per
  omega

/-- Valid WHIR schedules with positive queries have framed typed messages and draws. -/
theorem whirPresentation_framed {n : ℕ} (schedule : Whir.Schedule K n)
    (security : Whir.SecurityParameters schedule)
    (valid : schedule.Valid (algebraMap K E) security) (queries : positiveQueries schedule) :
    (whirPresentation schedule).Framed := by
  have quadratic : HashChain.PrefixFree quadraticEvents := by
    apply fieldEvents_framed
    intro a b equal
    apply Prod.ext (congrFun equal 0)
    funext i
    fin_cases i
    exact congrFun equal 1
  change (whirWirePresentation schedule).Framed
  induction schedule with
  | last lanes tail encoding count =>
      refine ⟨by decide, whirRounds_framed _ ?_ lanes⟩
      refine ⟨quadratic, fun _ => ⟨plaintextEvents_framed _, fun _ => ?_⟩⟩
      exact ⟨queryDraw_positive count _ queries (by have := valid.2.2.1.rate_pos; omega)
        valid.2.2.1.dimension_le, by decide, whirRounds_framed .done trivial tail⟩
  | more lanes encoding count rest ih =>
      refine ⟨by decide, whirRounds_framed _ ?_ lanes⟩
      refine ⟨quadratic, fun _ => ⟨?_, ?_, fun _ => ⟨quadratic, fun _ => ?_⟩⟩⟩
      · exact valid.2.1.1
      · apply fieldEvents_framed
        intro a b equal
        exact congrFun equal 0
      · exact ⟨queryDraw_positive count _ queries.1 (by have := valid.2.2.1.rate_pos; omega)
          valid.2.2.1.dimension_le, ih security.2 valid.2.2.2.2 queries.2⟩

/-- Framed typed observers recover each challenge-erased prefix from its events. -/
theorem WireObserver.encodeFrom_injective : {protocol : Protocol} →
    (coin : PublicCoin protocol) → (observer : WireObserver coin) → Framed coin observer →
    Function.Injective (encodeFrom coin observer)
  | _, .done, _, _, pre, _, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, observer, framed, ⟨a, pre⟩, ⟨b, pre'⟩, equal => by
      obtain ⟨rfl, rest⟩ := framed.1 a b _ _ equal
      have same := encodeFrom_injective (next a) (observer.2 a) (framed.2 a) rest
      cases same
      rfl
  | _, @PublicCoin.oracle _ _ _ _ next, observer, framed, ⟨a, pre⟩, ⟨b, pre'⟩, equal => by
      obtain ⟨rfl, rest⟩ := framed.1 a b _ _ equal
      have same := encodeFrom_injective next observer.2 framed.2 rest
      cases same
      rfl
  | _, @PublicCoin.challenge _ _ _ next, observer, framed, pre, pre', equal => by
      rcases pre with ⟨⟩ | ⟨⟨⟩, pre⟩ <;> rcases pre' with ⟨⟩ | ⟨⟨⟩, pre'⟩
      · rfl
      · change [] = List.replicate observer.1.width .squeeze ++ encodeFrom next observer.2 pre' at equal
        have lengths := congrArg List.length equal
        simp only [List.length_nil, List.length_append, List.length_replicate] at lengths
        have := framed.1
        omega
      · change List.replicate observer.1.width .squeeze ++ encodeFrom next observer.2 pre = [] at equal
        have lengths := congrArg List.length equal
        simp only [List.length_nil, List.length_append, List.length_replicate] at lengths
        have := framed.1
        omega
      · have rest := List.append_cancel_left (by exact equal)
        have same := encodeFrom_injective next observer.2 framed.2 rest
        cases same
        rfl

/-- Framing establishes injectivity before permutation, without any claim of hash injectivity. -/
theorem WireObserver.encode_injective {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (observer : (statement : Statement) → WireObserver (coin statement))
    (framed : ∀ statement, Framed (coin statement) (observer statement)) :
    Function.Injective (WireObserver.encode observer) := by
  rintro ⟨statement, pre⟩ ⟨statement', pre'⟩ equal
  obtain ⟨rfl, equal⟩ := Prod.mk.inj equal
  have same := encodeFrom_injective (coin statement) (observer statement) (framed statement) equal
  cases same
  rfl

end CompStark.Compiled
