/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.Interaction.Oracle.Security.BcsKnowledge
public import CompStark.Fs.HashChain
public import CompStark.Fs.MerkleLog
public import CompStark.Fs.Stark
public import CompStark.Fs.StarkTerminal

/-! # Plonky3's verifier draws its challenges as the real completion

The BCS game on the duplex chain (`Bcs.realExecution`) completes the adversary's selection of the
decoded snapshot protocol: each challenge's coins are the squeezes of its key's real chain inputs
(`realEncode`), its block's input and the blocks before it, each further squeeze absorbing the empty
input. A selection is read off a Plonky3 proof, and its completion draws exactly the challenges
Plonky3's verifier samples.

* `Statement.parse`: the selection's messages read off a proof at an admitted length, every
  snapshot move `T`: the length, the trace's cap (`capVec`: `none` unless the cap has the size the
  verifier accepts), `α`'s empty witness, the quotient's cap and the out-of-domain witness, the
  claimed values (`Fs.openingsOf`) and the batching witness, FRI's caps and commit witnesses, the
  final polynomial and the query witness (`parseFri`). Its input is the preprocessed commitment's
  elements and the public values (`Statement.inputOf`).
* `openedPath`, `replay_realCompletion`: the path that completing messages of a snapshot protocol on
  deterministic coins decodes and opens to, for any protocol.
* `duplexCache`, `squeezeAnswer`, `sample_sampleStates`: the duplex answers as the chain, and
  Plonky3's challenger as a stream of squeezes: from the capacity of the absorbed blocks, sample
  `q K + r` is sample `r` of squeeze `q`. `extDraw_idealOf`, `queryDraw_idealOf`: Plonky3's
  grinding check, extension sample and query samples are the draws on the squeezes' coins.
* `Setup.openedPath_parse`: if Plonky3's verifier on the duplex answers accepts, the real
  completion of the proof's selection, replayed on the duplex answers, decodes, every draw
  accepting, and opens to the proof's execution path (`Setup.proofPath`).
* `Statement.isSome_parse`, `Statement.length_preprocessedDigest`: an accepted proof has a
  selection, and its preprocessed commitment the statement's length.
-/

@[expose] public section

namespace CompStark.Fs
open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

/-! ### Completing snapshot messages on deterministic coins -/

section Generic

variable {F Snap C : Type} [DecidableEq Snap] [SampleableType C]

/-- The path of the protocol that the duplex verifier's completion of messages of the snapshot
protocol decodes and opens to, each challenge's coins `coins r n` read off its real chain inputs
`r` (its block's input and the inputs before it, latest first) with its `n` squeezes: after the
real elements `pending` observed since the last squeeze, `tail` observed at the first squeeze,
the completed inputs `acc`, and the latest snapshot `T`; `none` if a draw rejects its coins. -/
def openedPath (coins : List F × List (List F) → ℕ → C) : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap coin dec) →
    (start : Bool) → Snap → (pending tail : List F) → (acc : List (List F)) →
    Messages PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)) →
    Option protocol.tree.ExecutionPath
  | _, .done, _, _, _, _, _, _, _, _ => some PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, pending, tail, acc, msgs =>
      (openedPath coins (next msgs.2.1) (dec msgs.2.1) (lay.2 msgs.2.1) false msgs.1
        (pending ++ lay.1 msgs.2.1) tail acc msgs.2.2).map fun rest => ⟨msgs.2.1, rest⟩
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, pending, tail, acc, msgs =>
      (openedPath coins (next msgs.1) (dec msgs.1) (lay.2 msgs.1) false T
        (pending ++ lay.1 msgs.1) tail acc msgs.2).map fun rest => ⟨msgs.1, rest⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, _, pending, tail, acc, msgs =>
      (openedPath coins next dec lay.2 false msgs.1 (pending ++ lay.1.observe msgs.2.1) tail acc
        msgs.2.2).map fun rest => ⟨lay.1.open msgs.1 msgs.2.1, rest⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, T, pending, tail, acc, msgs =>
      (openedPath coins next dec lay.2 false T (pending ++ lay.1.observe msgs.1) tail acc
        msgs.2).map fun rest => ⟨lay.1.open T msgs.1, rest⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, pending, tail, acc, msgs =>
      bif dec.1.accept (coins (pending ++ tail ++ lay.2.1 msgs.2.1, acc) lay.1) then
        (if lay.1 = 0 then
          openedPath coins next dec.2 lay.2.2 (lay.1 != 0) msgs.1 (pending ++ lay.2.1 msgs.2.1)
            tail acc msgs.2.2.2
        else openedPath coins next dec.2 lay.2.2 (lay.1 != 0) msgs.1 [] []
          (List.replicate (lay.1 - 1) [] ++ (pending ++ tail ++ lay.2.1 msgs.2.1) :: acc)
          msgs.2.2.2).map fun rest =>
            ⟨dec.1.decode (coins (pending ++ tail ++ lay.2.1 msgs.2.1, acc) lay.1), rest⟩
      else none
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, pending, tail, acc, msgs =>
      bif dec.1.accept (coins (pending ++ tail ++ lay.2.1 msgs.1, acc) lay.1) then
        (if lay.1 = 0 then
          openedPath coins next dec.2 lay.2.2 (lay.1 != 0) T (pending ++ lay.2.1 msgs.1) tail acc
            msgs.2.2
        else openedPath coins next dec.2 lay.2.2 (lay.1 != 0) T [] []
          (List.replicate (lay.1 - 1) [] ++ (pending ++ tail ++ lay.2.1 msgs.1) :: acc)
          msgs.2.2).map fun rest =>
            ⟨dec.1.decode (coins (pending ++ tail ++ lay.2.1 msgs.1, acc) lay.1), rest⟩
      else none

/-! #### Steps of `openedPath` inside a block -/

section Steps
variable (coins : List F × List (List F) → ℕ → C)

theorem openedPath_sender {Moves : Type} {inst : DecidableEq Moves} {rest : Moves → Protocol.{0}}
    (next : (m : Moves) → PublicCoin (rest m))
    (dec : Decoder C (@PublicCoin.sender Moves inst rest next))
    (lay : Layout F Snap (@PublicCoin.sender Moves inst rest next) dec) (T : Snap)
    (pending tail : List F) (acc : List (List F)) (mv : Moves)
    (msgs : Messages PUnit (decoded C (snapCoin (next mv) (dec mv) (lay.2 mv) false)
      (snapDecoder (next mv) (dec mv) (lay.2 mv) false))) :
    openedPath coins (@PublicCoin.sender Moves inst rest next) dec lay false T pending tail acc
        (⟨mv, msgs⟩ : (mv : Moves) × Messages PUnit (decoded C
          (snapCoin (next mv) (dec mv) (lay.2 mv) false)
          (snapDecoder (next mv) (dec mv) (lay.2 mv) false))) =
      (openedPath coins (next mv) (dec mv) (lay.2 mv) false T (pending ++ lay.1 mv) tail acc
        msgs).map fun r => ⟨mv, r⟩ := rfl

theorem openedPath_oracle {M : Type} [DecidableEq M]
    {interface : OracleInterface.{0, 0} M} {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (@PublicCoin.oracle M _ interface rest next))
    (lay : Layout F Snap (.oracle next) dec) (T : Snap) (pending tail : List F)
    (acc : List (List F)) (com : lay.1.Com)
    (msgs : Messages PUnit (decoded C (snapCoin next dec lay.2 false)
      (snapDecoder next dec lay.2 false))) :
    openedPath coins (.oracle next) dec lay false T pending tail acc
        (⟨com, msgs⟩ : (_ : lay.1.Com) × Messages PUnit (decoded C (snapCoin next dec lay.2 false)
          (snapDecoder next dec lay.2 false))) =
      (openedPath coins next dec lay.2 false T (pending ++ lay.1.observe com) tail acc
        msgs).map fun r => ⟨lay.1.open T com, r⟩ := rfl

/-- A challenge that squeezes, whose draw accepts its coins, decodes them and starts a block: its
block's real input `x` the pending elements, the tail and the witness's. -/
theorem openedPath_challenge {Challenge : Type} [SampleableType Challenge]
    {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (.challenge (Challenge := Challenge) next))
    (lay : Layout F Snap (.challenge next) dec) (T : Snap) (pending tail : List F)
    (acc : List (List F)) (w : dec.1.Witness) (u : PUnit)
    (msgs : Messages PUnit (decoded C (snapCoin next dec.2 lay.2.2 (lay.1 != 0))
      (snapDecoder next dec.2 lay.2.2 (lay.1 != 0)))) (x : List F)
    (hx : pending ++ tail ++ lay.2.1 w = x) (h0 : lay.1 ≠ 0)
    (hacc : dec.1.accept (coins (x, acc) lay.1) = true) :
    openedPath coins (.challenge next) dec lay false T pending tail acc
        (⟨w, u, msgs⟩ : (_ : dec.1.Witness) × (PUnit × Messages PUnit (decoded C
          (snapCoin next dec.2 lay.2.2 (lay.1 != 0)) (snapDecoder next dec.2 lay.2.2 _)))) =
      (openedPath coins next dec.2 lay.2.2 (lay.1 != 0) T [] []
        (List.replicate (lay.1 - 1) [] ++ x :: acc) msgs).map
        fun r => ⟨dec.1.decode (coins (x, acc) lay.1), r⟩ := by
  subst hx
  simp only [openedPath, hacc, Bool.cond_true, h0, ↓reduceIte]

end Steps

/-- Replaying a sequence of squeezes, each replayed to its answer. -/
theorem replay_squeezeAnswers_eq {S O ι : Type} {spec : OracleSpec ι} (c : spec.QueryCache)
    {answer : ℕ → OracleComp (unifSpec + spec) (S × O)} {value : ℕ → S × O}
    (h : ∀ j, replay c (answer j) = some (value j)) :
    ∀ n, replay c (squeezeAnswers answer n) = some ((List.range n).map value)
  | 0 => by simp only [squeezeAnswers, replay_pure, List.range_zero, List.map_nil]
  | n + 1 => by
    rw [squeezeAnswers, replay_bind, replay_squeezeAnswers_eq c h n]
    change (replay c (answer n >>= fun a => pure _)) = _
    rw [replay_bind, h n]
    simp only [replay_pure, List.range_succ, List.map_append, List.map_singleton]
    rfl

/-- A replayed program's result is kept on a larger cache. -/
theorem replay_mono {ι : Type} {spec : OracleSpec ι} {c c' : spec.QueryCache}
    (hc : ∀ t u, c t = some u → c' t = some u) {α : Type} :
    ∀ (P : OracleComp (unifSpec + spec) α) (a : α), replay c P = some a → replay c' P = some a
  := by
  intro P
  induction P using OracleComp.inductionOn with
  | pure b => exact fun a h => h
  | query_bind t k ih =>
    intro a h
    rw [replay_query_bind] at h ⊢
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    rcases t with n | t
    · exact absurd hu (by simp [cacheAnswers])
    · exact Option.bind_eq_some_iff.mpr ⟨u, hc t u hu, ih u a h⟩

omit [DecidableEq Snap] [SampleableType C] in
/-- The real inputs of a block: the erased elements before the witness, then the witness's. -/
theorem eraseInputs_block (pending tail : List (F ⊕ Snap)) (x : List F)
    (acc : List (List (F ⊕ Snap))) :
    eraseInputs (pending ++ tail ++ x.map .inl, acc) =
      (erase pending ++ erase tail ++ x, acc.map erase) := by
  simp only [eraseInputs, erase_append, erase_map_inl]

omit [DecidableEq Snap] [SampleableType C] in
/-- Erasing elements of `F` after other elements keeps them. -/
theorem erase_append_map_inl (pending : List (F ⊕ Snap)) (x : List F) :
    erase (pending ++ x.map .inl) = erase pending ++ x := by
  simp only [erase_append, erase_map_inl]

omit [DecidableEq Snap] [SampleableType C] in
/-- Erasing completed inputs with empty extra squeezes keeps the empty inputs. -/
theorem map_erase_replicate (k : ℕ) (b : List (F ⊕ Snap)) (acc : List (List (F ⊕ Snap))) :
    (List.replicate k [] ++ b :: acc).map erase = List.replicate k [] ++ erase b :: acc.map erase
  := by
  simp only [List.map_append, List.map_replicate, erase_nil, List.map_cons]

/-! #### Decoding and opening a step of a path of the snapshot protocol -/

omit [SampleableType C] in
theorem decodeOpen_sender_false {Moves : Type} [DecidableEq Moves] {rest : Moves → Protocol.{0}}
    (next : (m : Moves) → PublicCoin (rest m)) (dec : Decoder C (.sender next))
    (lay : Layout F Snap (.sender next) dec) (T : Snap) (m : Moves)
    (path : (decodedProtocol C (snapCoin (next m) (dec m) (lay.2 m) false)
      (snapDecoder (next m) (dec m) (lay.2 m) false)).tree.ExecutionPath) :
    (decodePath (snapCoin (.sender next) dec lay false) (snapDecoder (.sender next) dec lay false)
      ⟨m, path⟩).map (openPath (.sender next) dec lay false T) =
    ((decodePath _ _ path).map (openPath (next m) (dec m) (lay.2 m) false T)).map
      fun r => ⟨m, r⟩ := by
  refine (Option.map_map _ _ _).trans ?_
  dsimp only
  change Option.map _ (decodePath (snapCoin (next m) (dec m) (lay.2 m) false)
    (snapDecoder (next m) (dec m) (lay.2 m) false) path) = _
  cases decodePath (snapCoin (next m) (dec m) (lay.2 m) false)
    (snapDecoder (next m) (dec m) (lay.2 m) false) path <;> rfl

omit [SampleableType C] in
theorem decodeOpen_sender_true {Moves : Type} [DecidableEq Moves] {rest : Moves → Protocol.{0}}
    (next : (m : Moves) → PublicCoin (rest m)) (dec : Decoder C (.sender next))
    (lay : Layout F Snap (.sender next) dec) (T T' : Snap) (m : Moves)
    (path : (decodedProtocol C (snapCoin (next m) (dec m) (lay.2 m) false)
      (snapDecoder (next m) (dec m) (lay.2 m) false)).tree.ExecutionPath) :
    (decodePath (snapCoin (.sender next) dec lay true) (snapDecoder (.sender next) dec lay true)
      ⟨T', m, path⟩).map (openPath (.sender next) dec lay true T) =
    ((decodePath _ _ path).map (openPath (next m) (dec m) (lay.2 m) false T')).map
      fun r => ⟨m, r⟩ := by
  change Option.map _ (Option.map _ (Option.map _ (decodePath (snapCoin (next m) (dec m)
    (lay.2 m) false) (snapDecoder (next m) (dec m) (lay.2 m) false) path))) = _
  cases decodePath (snapCoin (next m) (dec m) (lay.2 m) false)
    (snapDecoder (next m) (dec m) (lay.2 m) false) path <;> rfl

omit [SampleableType C] in
theorem decodeOpen_oracle_false {Messages : Type} [DecidableEq Messages]
    {interface : OracleInterface.{0, 0} Messages} {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (@PublicCoin.oracle Messages _ interface rest next))
    (lay : Layout F Snap (.oracle next) dec) (T : Snap) (com : lay.1.Com)
    (path : (decodedProtocol C (snapCoin next dec lay.2 false)
      (snapDecoder next dec lay.2 false)).tree.ExecutionPath) :
    (decodePath (snapCoin (.oracle next) dec lay false) (snapDecoder (.oracle next) dec lay false)
      ⟨com, path⟩).map (openPath (.oracle next) dec lay false T) =
    ((decodePath _ _ path).map (openPath next dec lay.2 false T)).map
      fun r => ⟨lay.1.open T com, r⟩ := by
  change Option.map _ (Option.map _ (decodePath (snapCoin next dec lay.2 false)
    (snapDecoder next dec lay.2 false) path)) = _
  cases decodePath (snapCoin next dec lay.2 false) (snapDecoder next dec lay.2 false) path <;> rfl

omit [SampleableType C] in
theorem decodeOpen_oracle_true {Messages : Type} [DecidableEq Messages]
    {interface : OracleInterface.{0, 0} Messages} {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (@PublicCoin.oracle Messages _ interface rest next))
    (lay : Layout F Snap (.oracle next) dec) (T T' : Snap) (com : lay.1.Com)
    (path : (decodedProtocol C (snapCoin next dec lay.2 false)
      (snapDecoder next dec lay.2 false)).tree.ExecutionPath) :
    (decodePath (snapCoin (.oracle next) dec lay true) (snapDecoder (.oracle next) dec lay true)
      ⟨T', com, path⟩).map (openPath (.oracle next) dec lay true T) =
    ((decodePath _ _ path).map (openPath next dec lay.2 false T')).map
      fun r => ⟨lay.1.open T' com, r⟩ := by
  change Option.map _ (Option.map _ (Option.map _ (decodePath (snapCoin next dec lay.2 false)
    (snapDecoder next dec lay.2 false) path))) = _
  cases decodePath (snapCoin next dec lay.2 false) (snapDecoder next dec lay.2 false) path <;> rfl

omit [SampleableType C] in
theorem decodeOpen_challenge_false {Challenge : Type} [SampleableType Challenge]
    {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (.challenge (Challenge := Challenge) next))
    (lay : Layout F Snap (.challenge next) dec) (T : Snap) (w : dec.1.Witness) (ch : C)
    (path : (decodedProtocol C (snapCoin next dec.2 lay.2.2 (lay.1 != 0))
      (snapDecoder next dec.2 lay.2.2 (lay.1 != 0))).tree.ExecutionPath) :
    (decodePath (snapCoin (.challenge next) dec lay false)
      (snapDecoder (.challenge next) dec lay false) ⟨w, ch, path⟩).map
        (openPath (.challenge next) dec lay false T) =
    bif dec.1.accept ch then
      ((decodePath _ _ path).map (openPath next dec.2 lay.2.2 (lay.1 != 0) T)).map
        fun r => ⟨dec.1.decode ch, r⟩
    else none := by
  change Option.map _ (bif dec.1.accept ch then Option.map _ (decodePath (snapCoin next dec.2
    lay.2.2 (lay.1 != 0)) (snapDecoder next dec.2 lay.2.2 (lay.1 != 0)) path) else none) = _
  cases dec.1.accept ch
  · rfl
  · cases decodePath (snapCoin next dec.2 lay.2.2 (lay.1 != 0))
      (snapDecoder next dec.2 lay.2.2 (lay.1 != 0)) path <;> rfl

omit [SampleableType C] in
theorem decodeOpen_challenge_true {Challenge : Type} [SampleableType Challenge]
    {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (.challenge (Challenge := Challenge) next))
    (lay : Layout F Snap (.challenge next) dec) (T T' : Snap)
    (path : (decodedProtocol C (snapCoin (.challenge next) dec lay false)
      (snapDecoder (.challenge next) dec lay false)).tree.ExecutionPath) :
    (decodePath (snapCoin (.challenge next) dec lay true)
      (snapDecoder (.challenge next) dec lay true) ⟨T', path⟩).map
        (openPath (.challenge next) dec lay true T) =
    (decodePath _ _ path).map (openPath (.challenge next) dec lay false T') := by
  change Option.map _ (Option.map _ (decodePath (snapCoin (.challenge next) dec lay false)
    (snapDecoder (.challenge next) dec lay false) path)) = _
  cases decodePath (snapCoin (.challenge next) dec lay false)
    (snapDecoder (.challenge next) dec lay false) path <;> rfl

/-- Replaying a completion step mapped inside `Option`. -/
theorem replay_map_option {ι : Type} {spec : OracleSpec ι} (c : spec.QueryCache) {α β : Type}
    (f : α → β) (P : OracleComp (unifSpec + spec) (Option α)) (r : α)
    (h : replay c P = some (some r)) : replay c (Option.map f <$> P) = some (some (f r)) := by
  rw [replay_map, h]
  rfl

/-- Replaying a bind whose first program replays to `a`. -/
theorem replay_bind_of {ι : Type} {spec : OracleSpec ι} {c : spec.QueryCache} {α β : Type}
    {P : OracleComp (unifSpec + spec) α} {k : α → OracleComp (unifSpec + spec) β} {a : α}
    {b : β} (hP : replay c P = some a) (hk : replay c (k a) = some b) :
    replay c (P >>= k) = some b := by
  rw [replay_bind, hP]
  exact hk

/-- **Completing snapshot messages on deterministic coins.** If the coins `Q` at every prefix
replay on `c` to `coins` of the prefix's real chain inputs and squeezes, completing messages
replays to a path that decodes and opens, on the latest snapshot `T`, to `openedPath`. -/
theorem replay_coinQueries {ι : Type} {spec : OracleSpec ι} (c : spec.QueryCache)
    (coins : List F × List (List F) → ℕ → C) : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap coin dec) →
    (start : Bool) → (T : Snap) → (pending tail : List (F ⊕ Snap)) →
    (acc : List (List (F ⊕ Snap))) →
    (Q : Prefix PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)) →
      OracleComp (unifSpec + spec) C) →
    (∀ pre, replay c (Q pre) = some (coins (eraseInputs
      ((snapObserver coin dec lay start).encodeFrom _ _ pending tail acc pre))
      ((snapObserver coin dec lay start).squeezes _ _ (Prefix.undecode _ _ pre)))) →
    (msgs : Messages PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))) →
    ∃ path, replay c (simulateQ (coinQueries _ _ Q)
        (stoppedCompletePrefix _ (GuardSchedule.pass _) msgs)) = some (some path) ∧
      (decodePath _ _ path).map (openPath coin dec lay start T) =
        openedPath coins coin dec lay start T (erase pending) (erase tail) (acc.map erase) msgs
  | _, .done, _, _, _, _, _, _, _, _, _, _ => ⟨PUnit.unit, by
      change replay c (simulateQ _ (pure (some PUnit.unit))) = _
      simp only [simulateQ_pure, replay_pure]
      rfl, rfl⟩
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, T, pending, tail, acc, Q, hQ, msgs => by
      cases start
      · obtain ⟨path, hp, hd⟩ := replay_coinQueries c coins (next msgs.1) (dec msgs.1)
          (lay.2 msgs.1) false T (pending ++ (lay.1 msgs.1).map (Sum.inl : F → F ⊕ Snap)) tail
          acc (fun q => Q ⟨msgs.1, q⟩) (fun q => hQ ⟨msgs.1, q⟩) msgs.2
        refine ⟨⟨msgs.1, path⟩, ?_, ?_⟩
        · exact (congrArg (replay c) (simulateQ_coinQueries_sender
            (fun m => snapCoin (next m) (dec m) (lay.2 m) false)
            (snapDecoder (.sender next) dec lay false) Q msgs)).trans
            (replay_map_option c _ _ _ hp)
        · rw [decodeOpen_sender_false, hd, erase_append_map_inl]
          rfl
      · obtain ⟨path, hp, hd⟩ := replay_coinQueries c coins (next msgs.2.1) (dec msgs.2.1)
          (lay.2 msgs.2.1) false msgs.1
          (pending ++ [(Sum.inr msgs.1 : F ⊕ Snap)] ++ (lay.1 msgs.2.1).map Sum.inl) tail acc
          (fun q => Q ⟨msgs.1, msgs.2.1, q⟩) (fun q => hQ ⟨msgs.1, msgs.2.1, q⟩) msgs.2.2
        refine ⟨⟨msgs.1, msgs.2.1, path⟩, ?_, ?_⟩
        · refine (congrArg (replay c) (simulateQ_coinQueries_sender
            (fun _ : Snap => snapCoin (.sender next) dec lay false)
            (snapDecoder (.sender next) dec lay true) Q msgs)).trans
            (replay_map_option c _ _ _ ?_)
          exact (congrArg (replay c) (simulateQ_coinQueries_sender
            (fun m => snapCoin (next m) (dec m) (lay.2 m) false)
            (snapDecoder (.sender next) dec lay false) (fun q => Q ⟨msgs.1, q⟩) msgs.2)).trans
            (replay_map_option c _ _ _ hp)
        · rw [decodeOpen_sender_true, hd, erase_append_map_inl, erase_append, erase_cons_inr,
            erase_nil, List.append_nil]
          rfl
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start, T, pending, tail, acc, Q, hQ, msgs => by
      cases start
      · obtain ⟨path, hp, hd⟩ := replay_coinQueries c coins next dec lay.2 false T
          (pending ++ (lay.1.observe msgs.1).map (Sum.inl : F → F ⊕ Snap)) tail acc
          (fun q => Q ⟨msgs.1, q⟩) (fun q => hQ ⟨msgs.1, q⟩) msgs.2
        refine ⟨⟨msgs.1, path⟩, ?_, ?_⟩
        · exact (congrArg (replay c) (simulateQ_coinQueries_sender
            (fun _ : lay.1.Com => snapCoin next dec lay.2 false)
            (snapDecoder (.oracle next) dec lay false) Q msgs)).trans
            (replay_map_option c _ _ _ hp)
        · rw [decodeOpen_oracle_false, hd, erase_append_map_inl]
          rfl
      · obtain ⟨path, hp, hd⟩ := replay_coinQueries c coins next dec lay.2 false msgs.1
          (pending ++ [(Sum.inr msgs.1 : F ⊕ Snap)] ++ (lay.1.observe msgs.2.1).map Sum.inl) tail
          acc (fun q => Q ⟨msgs.1, msgs.2.1, q⟩) (fun q => hQ ⟨msgs.1, msgs.2.1, q⟩) msgs.2.2
        refine ⟨⟨msgs.1, msgs.2.1, path⟩, ?_, ?_⟩
        · refine (congrArg (replay c) (simulateQ_coinQueries_sender
            (fun _ : Snap => snapCoin (.oracle next) dec lay false)
            (snapDecoder (.oracle next) dec lay true) Q msgs)).trans
            (replay_map_option c _ _ _ ?_)
          exact (congrArg (replay c) (simulateQ_coinQueries_sender
            (fun _ : lay.1.Com => snapCoin next dec lay.2 false)
            (snapDecoder (.oracle next) dec lay false) (fun q => Q ⟨msgs.1, q⟩) msgs.2)).trans
            (replay_map_option c _ _ _ hp)
        · rw [decodeOpen_oracle_true, hd, erase_append_map_inl, erase_append, erase_cons_inr,
            erase_nil, List.append_nil]
          rfl
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, T, pending, tail, acc, Q, hQ, msgs => by
      have hf : ∀ (T : Snap) (pending : List (F ⊕ Snap)) (Q : Prefix PUnit (decoded C
            (snapCoin (.challenge next) dec lay false)
            (snapDecoder (.challenge next) dec lay false)) → OracleComp (unifSpec + spec) C),
          (∀ pre, replay c (Q pre) = some (coins (eraseInputs
            ((snapObserver (.challenge next) dec lay false).encodeFrom _ _ pending tail acc pre))
            ((snapObserver (.challenge next) dec lay false).squeezes _ _
              (Prefix.undecode _ _ pre)))) →
          ∀ msgs, ∃ path, replay c (simulateQ (coinQueries _ _ Q)
              (stoppedCompletePrefix _ (GuardSchedule.pass _) msgs)) = some (some path) ∧
            (decodePath _ _ path).map (openPath (.challenge next) dec lay false T) =
              openedPath coins (.challenge next) dec lay false T (erase pending) (erase tail)
                (acc.map erase) msgs := by
        intro T pending Q hQ msgs
        have hc0 : replay c (Q ⟨msgs.1, .inl msgs.2.1⟩) = some (coins (erase pending ++
            erase tail ++ lay.2.1 msgs.1, acc.map erase) lay.1) :=
          (hQ ⟨msgs.1, .inl msgs.2.1⟩).trans (congrArg (fun r => some (coins r lay.1))
            (eraseInputs_block pending tail (lay.2.1 msgs.1) acc))
        have hstep : ∀ path, replay c (simulateQ (coinQueries _ _ fun q =>
              Q ⟨msgs.1, .inr ⟨msgs.2.1, q⟩⟩) (stoppedCompletePrefix _ (GuardSchedule.pass _)
                msgs.2.2)) = some (some path) →
            replay c (simulateQ (coinQueries _ _ Q)
              (stoppedCompletePrefix _ (GuardSchedule.pass _) msgs)) =
              some (some ⟨msgs.1, coins (erase pending ++ erase tail ++ lay.2.1 msgs.1,
                acc.map erase) lay.1, path⟩) := fun path hp => by
          refine (congrArg (replay c) (simulateQ_coinQueries_challenge
            (snapCoin next dec.2 lay.2.2 (lay.1 != 0))
            (snapDecoder (.challenge next) dec lay false) Q msgs)).trans ?_
          exact replay_bind_of hc0 (replay_map_option c _ _ _ hp)
        by_cases h0 : lay.1 = 0
        · obtain ⟨path, hp, hd⟩ := replay_coinQueries c coins next dec.2 lay.2.2 (lay.1 != 0) T
            (pending ++ (lay.2.1 msgs.1).map (Sum.inl : F → F ⊕ Snap)) tail acc
            (fun q => Q ⟨msgs.1, .inr ⟨msgs.2.1, q⟩⟩)
            (fun q => (hQ ⟨msgs.1, .inr ⟨msgs.2.1, q⟩⟩).trans
              (congrArg (fun r => some (coins (eraseInputs r)
                ((snapObserver next dec.2 lay.2.2 (lay.1 != 0)).squeezes _ _
                  (Prefix.undecode _ _ q))))
                ((encodeFrom_snap_challenge next dec lay pending tail acc msgs.1 msgs.2.1
                  q).trans (ite_eq_left h0)))) msgs.2.2
          refine ⟨_, hstep path hp, ?_⟩
          refine (decodeOpen_challenge_false next dec lay T msgs.1 _ path).trans ?_
          rw [hd, erase_append_map_inl]
          simp only [openedPath, ite_eq_left h0]
        · obtain ⟨path, hp, hd⟩ := replay_coinQueries c coins next dec.2 lay.2.2 (lay.1 != 0) T
            [] [] (List.replicate (lay.1 - 1) [] ++
              (pending ++ tail ++ (lay.2.1 msgs.1).map (Sum.inl : F → F ⊕ Snap)) :: acc)
            (fun q => Q ⟨msgs.1, .inr ⟨msgs.2.1, q⟩⟩)
            (fun q => (hQ ⟨msgs.1, .inr ⟨msgs.2.1, q⟩⟩).trans
              (congrArg (fun r => some (coins (eraseInputs r)
                ((snapObserver next dec.2 lay.2.2 (lay.1 != 0)).squeezes _ _
                  (Prefix.undecode _ _ q))))
                ((encodeFrom_snap_challenge next dec lay pending tail acc msgs.1 msgs.2.1
                  q).trans (ite_eq_right h0)))) msgs.2.2
          refine ⟨_, hstep path hp, ?_⟩
          refine (decodeOpen_challenge_false next dec lay T msgs.1 _ path).trans ?_
          rw [hd, map_erase_replicate, erase_nil, erase_append, erase_append, erase_map_inl]
          simp only [openedPath, ite_eq_right h0]
      cases start
      · exact hf T pending Q hQ msgs
      · obtain ⟨path, hp, hd⟩ := hf msgs.1 (pending ++ [(Sum.inr msgs.1 : F ⊕ Snap)])
          (fun q => Q ⟨msgs.1, q⟩) (fun q => hQ ⟨msgs.1, q⟩) msgs.2
        refine ⟨⟨msgs.1, path⟩, ?_, ?_⟩
        · exact (congrArg (replay c) (simulateQ_coinQueries_sender
            (fun _ : Snap => snapCoin (.challenge next) dec lay false)
            (snapDecoder (.challenge next) dec lay true) Q msgs)).trans
            (replay_map_option c _ _ _ hp)
        · rw [decodeOpen_challenge_true, hd, erase_append, erase_cons_inr, erase_nil,
            List.append_nil]
          rfl

end Generic

section Completion

variable {S O : Type} [SampleableType S] [SampleableType O] [Inhabited S] [Inhabited O] {m : ℕ}
  {F : Type} {ι : Type} {hs : OracleSpec ι} [DecidableEq hs.QueryCache]
  {Input W : Type} {protocol : Input → Protocol.{0}}

/-- **The duplex verifier's completion on deterministic answers.** If every squeeze replays on
the chain cache `c` to `sq` of its real inputs, the real completion of a selection replays to a
path that decodes and opens to `openedPath` on the squeezes' coins. -/
theorem replay_realCompletion (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (c : (chainSpec S (List F) O + []ₒ).QueryCache) (sq : List F → List (List F) → ℕ → S × O)
    (hc : ∀ x p j, replay c (squeezeAt s₀ [] x p j) = some (sq x p j)) (z : Input)
    (msgs : Messages PUnit (decoded (Fin m → S × O) (snapCoin (coin z) (dec z) (lay z) true)
      (snapDecoder (coin z) (dec z) (lay z) true))) (w : W) :
    ∃ path, replay c (realCompletion s₀ coin dec lay tail (some ⟨z, msgs, w⟩)) =
        some (some ⟨z, path, w⟩) ∧
      (decodePath _ _ path).map (openPath (coin z) (dec z) (lay z) true ∅) =
        openedPath (fun r n => coinsOf ((List.range n).map (sq r.1 r.2))) (coin z) (dec z)
          (lay z) true ∅ [] (tail z) [] msgs := by
  obtain ⟨path, hp, hd⟩ := replay_coinQueries c
    (fun r n => (coinsOf ((List.range n).map (sq r.1 r.2)) : Fin m → S × O)) (coin z) (dec z)
    (lay z) true ∅ [] ((tail z).map Sum.inl) []
    (fun pre => coinsOf <$> squeezeAnswers (squeezeAt s₀ []
        (realEncode coin dec lay tail ⟨z, pre⟩).1 (realEncode coin dec lay tail ⟨z, pre⟩).2)
      (keySqueezes (fun z => snapDecoder (coin z) (dec z) (lay z) true)
        (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _) ⟨z, pre⟩))
    (fun pre => by
      rw [replay_map, replay_squeezeAnswers_eq c (fun j => hc _ _ j)]
      rfl) msgs
  refine ⟨path, ?_, ?_⟩
  · simp only [realCompletion, squeezeCompletionAfter, stoppedComplete, simulateQ_reindexQuery]
    exact replay_map_option c _ _ _ hp
  · rw [hd, erase_nil, erase_map_inl, List.map_nil]

end Completion

end CompStark.Fs

/-! ### The duplex chain on an answer table -/

namespace CompStark.Fs
open CompStark.Stark CompStark.RandomOracle OracleComp OracleSpec
open Interaction.Oracle.Security.HashChain

section Chain
variable {F : Type} [BaseField F] {K : ℕ} (answer : (q : Query F) → Answer K q)

/-- The duplex answers as a cache of the chain: the squeeze at a capacity and an input. -/
def duplexCache : (duplexSpec F K + []ₒ).QueryCache :=
  QueryCache.ofFn fun t => match t with
    | .inl q => some (answer (.duplex q.1 q.2))
    | .inr e => nomatch e

/-- The answer of the `j`th squeeze after absorbing the blocks `x :: p`, latest first: the first
at the capacity of `p` and the input `x`, each further one at the previous capacity and the empty
input. -/
def squeezeAnswer (x : List F) (p : List (List F)) : ℕ → Digest F × Vector F K
  | 0 => answer (.duplex (capOf answer p) x)
  | j + 1 => answer (.duplex (squeezeAnswer x p j).1 [])

/-- The capacity after `j + 1` squeezes is the capacity of the blocks with `j` empty inputs. -/
theorem capOf_replicate (x : List F) (p : List (List F)) :
    ∀ j, capOf answer (List.replicate j [] ++ x :: p) = (squeezeAnswer answer x p j).1
  | 0 => rfl
  | j + 1 => by
    rw [List.replicate_succ, List.cons_append, capOf, capOf_replicate x p j]
    rfl

/-- Absorbing blocks through the chain replays on the duplex answers to the answer at the
blocks' capacity. -/
theorem replay_absorb (x : List F) :
    ∀ p, replay (duplexCache answer) (absorb initCap x p) =
      some (answer (.duplex (capOf answer p) x))
  | [] => Interaction.Oracle.Security.Bcs.replay_query _ _
  | y :: p => by
    rw [absorb]
    exact replay_bind_of (replay_absorb y p) (Interaction.Oracle.Security.Bcs.replay_query _ _)

/-- Every squeeze replays on the duplex answers to `squeezeAnswer`. -/
theorem replay_squeezeAt (x : List F) (p : List (List F)) :
    ∀ j, replay (duplexCache answer) (squeezeAt initCap [] x p j) =
      some (squeezeAnswer answer x p j)
  | 0 => replay_absorb answer x p
  | j + 1 => by
    rw [squeezeAt, squeezePrefix, replay_absorb, capOf_replicate]
    rfl

end Chain

/-! ### Plonky3's challenger as a stream of squeezes -/

section Stream
variable {F : Type} [BaseField F] {K : ℕ} (answer : (q : Query F) → Answer K q)

theorem headD_eq_getD (l : List F) : l.headD 0 = l.getD 0 0 := by
  cases l <;> rfl

/-- With a sample left at `r + 1`, the samples from `r + 1` on are it and those after it. -/
theorem drop_eq_getD_cons (v : Vector F K) {r : ℕ} (hr : r + 1 < K) :
    v.toList.drop (r + 1) = v.toList.getD (r + 1) 0 :: v.toList.drop (r + 2) := by
  have hl : r + 1 < v.toList.length := by rw [Vector.length_toList]; exact hr
  rw [List.drop_eq_getElem_cons hl, List.getD_eq_getElem _ _ hl]

/-- A sample with samples left takes the first. -/
theorem sample_idealOf_drop (cap : Digest F) (v : Vector F K) {r : ℕ} (hr : r + 1 < K) :
    (idealOf answer).sample ⟨cap, [], v.toList.drop (r + 1)⟩ =
      (v.toList.getD (r + 1) 0, ⟨cap, [], v.toList.drop (r + 2)⟩) := by
  rw [drop_eq_getD_cons v hr]
  rfl

/-- A sample without samples left squeezes at the capacity and the pending input. -/
theorem sample_idealOf_squeeze (cap : Digest F) (input : List F) :
    (idealOf answer).sample ⟨cap, input, []⟩ =
      ((answer (.duplex cap input)).2.toList.getD 0 0,
        ⟨(answer (.duplex cap input)).1, [], (answer (.duplex cap input)).2.toList.drop 1⟩) := by
  rw [Fs.sample_idealOf_nil, headD_eq_getD, List.drop_one]

/-- **Plonky3's challenger is a stream of squeezes.** From the capacity of the blocks `p` with `x`
pending and no sample left, sample `q K + r` (`r < K`) is sample `r` of squeeze `q`, and leaves
the capacity of squeeze `q`, no input, and the rest of its samples. -/
theorem sample_sampleStates (hK : 0 < K) (x : List F) (p : List (List F)) :
    ∀ q r, r < K → (idealOf answer).sample
      (Fs.sampleStates (idealOf answer) ⟨capOf answer p, x, []⟩ (q * K + r)) =
      ((squeezeAnswer answer x p q).2.toList.getD r 0,
        ⟨(squeezeAnswer answer x p q).1, [], (squeezeAnswer answer x p q).2.toList.drop (r + 1)⟩)
  | q, 0, _ => by
    cases q with
    | zero =>
      rw [Nat.zero_mul, Nat.add_zero]
      exact sample_idealOf_squeeze answer _ _
    | succ q =>
      have h := sample_sampleStates hK x p q (K - 1) (by omega)
      rw [show (q + 1) * K + 0 = q * K + (K - 1) + 1 by rw [Nat.succ_mul]; omega,
        Fs.sampleStates, h, show K - 1 + 1 = K by omega,
        List.drop_of_length_le (by rw [Vector.length_toList])]
      exact sample_idealOf_squeeze answer _ _
  | q, r + 1, hr => by
    have h := sample_sampleStates hK x p q r (by omega)
    rw [show q * K + (r + 1) = q * K + r + 1 by omega, Fs.sampleStates, h]
    exact sample_idealOf_drop answer _ _ hr

/-- Sample `i` from the capacity of `p` with `x` pending is sample `i % K` of squeeze `i / K`. -/
theorem sample_sampleStates' (hK : 0 < K) (x : List F) (p : List (List F)) (i : ℕ) :
    ((idealOf answer).sample
      (Fs.sampleStates (idealOf answer) ⟨capOf answer p, x, []⟩ i)).1 =
      (squeezeAnswer answer x p (i / K)).2.toList.getD (i % K) 0 := by
  have h := sample_sampleStates answer hK x p (i / K) (i % K) (Nat.mod_lt _ hK)
  rw [Nat.div_add_mod'] at h
  rw [h]

/-- After `i + 1` samples from the capacity of `p` with `x` pending, the capacity is that of
squeeze `i / K` and nothing is pending. -/
theorem sampleStates_succ_eq (hK : 0 < K) (x : List F) (p : List (List F)) (i : ℕ) :
    (Fs.sampleStates (idealOf answer) ⟨capOf answer p, x, []⟩ (i + 1)).cap =
        capOf answer (List.replicate (i / K) [] ++ x :: p) ∧
      (Fs.sampleStates (idealOf answer) ⟨capOf answer p, x, []⟩ (i + 1)).input = [] := by
  have h := sample_sampleStates answer hK x p (i / K) (i % K) (Nat.mod_lt _ hK)
  rw [Nat.div_add_mod'] at h
  rw [Fs.sampleStates, h, capOf_replicate]
  exact ⟨rfl, rfl⟩

end Stream

/-! ### The draws on the stream -/

section Draws
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}
  (answer : (q : Query F) → Answer K q)

local notation "𝕂" => Challenge.Spec EF

/-- The coins of a challenge squeezed `n` times after absorbing the blocks `x :: p`: the answers of
its squeezes, the default answer past them. -/
def streamCoins (x : List F) (p : List (List F)) (n : ℕ) : Coins F K m :=
  coinsOf ((List.range n).map (squeezeAnswer answer x p))

/-- Sample `i` of a challenge's coins is sample `i % K` of squeeze `i / K`, for a sample of its
squeezes. -/
theorem sampleAt_streamCoins {x : List F} {p : List (List F)} {n : ℕ} (hn : n ≤ m) {i : ℕ}
    (hi : i / K < n) :
    sampleAt (streamCoins (m := m) answer x p n) i =
      (squeezeAnswer answer x p (i / K)).2.toList.getD (i % K) 0 := by
  have hm : i / K < m := lt_of_lt_of_le hi hn
  have hc : ((List.range n).map (squeezeAnswer answer x p)).getD (i / K) default =
      squeezeAnswer answer x p (i / K) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi),
      List.getElem_map, List.getElem_range]
  simp only [sampleAt, hm, ↓reduceDIte, streamCoins, coinsOf, hc]

/-- Sample `i < n K` of a challenge's coins is the challenger's sample `i` from the capacity of
`p` with `x` pending. -/
theorem sampleAt_streamCoins_eq (hK : 0 < K) {x : List F} {p : List (List F)} {n : ℕ}
    (hn : n ≤ m) {i : ℕ} (hi : i < n * K) :
    sampleAt (streamCoins (m := m) answer x p n) i =
      ((idealOf answer).sample
        (Fs.sampleStates (idealOf answer) ⟨capOf answer p, x, []⟩ i)).1 := by
  rw [sampleAt_streamCoins answer hn ((Nat.div_lt_iff_lt_mul hK).mpr hi),
    sample_sampleStates' answer hK]

omit [BaseField F] in
/-- `n` samples are the samples along the challenger's states. -/
theorem smpList_eq {G : Primitives F Id} : ∀ (n : ℕ) (s : G.State),
    Fs.smpList G s n =
      ((List.range n).map fun i => (G.sample (Fs.sampleStates G s i)).1, Fs.sampleStates G s n)
  | 0, _ => rfl
  | n + 1, s => by
    rw [Fs.smpList, smpList_eq n, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Function.comp_def, Fs.sampleStates_sample]
    rfl

/-- The `⌈s / K⌉` squeezes of `s ≥ 1` samples less one are `(s - 1) / K`. -/
theorem squeezesFor_sub_one (hK : 0 < K) {s : ℕ} (hs : 0 < s) :
    squeezesFor K s - 1 = (s - 1) / K := by
  simp only [squeezesFor]
  rw [show s + K - 1 = s - 1 + K * 1 by omega, Nat.add_mul_div_left _ _ hK, Nat.add_sub_cancel]

/-- The samples `o, …, o + d - 1` as an extension element. -/
theorem toSpec_smpExt (s : Sponge F) :
    Challenge.toSpec (Fs.smpExt (EF := EF) (idealOf answer) s).1 =
      Fs.extEquiv fun j => ((idealOf answer).sample (Fs.sampleStates (idealOf answer) s j)).1 := by
  rw [Fs.smpExt, smpList_eq, Challenge.toSpec_ofCoeffs]
  congr 1
  funext j
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact j.isLt),
    List.getElem_map, List.getElem_range]
  rfl

/-- The witness of an extension draw from a grinding witness: none without grinding. -/
def extWitnessOf : (bits : ℕ) → F → (extDraw (F := F) (EF := EF) (K := K) (m := m) bits).Witness
  | 0, _ => PUnit.unit
  | _ + 1, w => w

/-- The witness of the query draw from a grinding witness: none without grinding. -/
def queryWitnessOf (top t : ℕ) :
    (bits : ℕ) → F → (queryDraw (F := F) (K := K) (m := m) top t bits).Witness
  | 0, _ => PUnit.unit
  | _ + 1, w => w

theorem extWitnessElems_extWitnessOf (bits : ℕ) (w : F) :
    extWitnessElems (EF := EF) (K := K) (m := m) bits (extWitnessOf bits w) =
      Fs.witnessInput bits w := by
  cases bits <;> rfl

omit [Challenge F EF] in
theorem queryWitnessElems_queryWitnessOf (top t bits : ℕ) (w : F) :
    queryWitnessElems (K := K) (m := m) top t bits (queryWitnessOf top t bits w) =
      Fs.witnessInput bits w := by
  cases bits <;> rfl

/-- **An extension draw on the stream.** From the capacity of the blocks `acc` with `x₀` pending,
Plonky3's grinding check and extension sample are the draw on the coins of the block `x₀` and the
witness: the check passes as the draw accepts, the sample is the decoded challenge, and the
challenger is left at the capacity after the draw's squeezes with nothing pending. -/
theorem extDraw_idealOf (hK : 0 < K) (bits : ℕ) (w : F) (x₀ : List F) (acc : List (List F))
    (hm : squeezesFor K (extSamples (EF := EF) bits) ≤ m) :
    (extDraw (F := F) (EF := EF) bits).accept (streamCoins (m := m) answer
        (x₀ ++ Fs.witnessInput bits w) acc
        (squeezesFor K (extSamples (EF := EF) bits))) =
        (Fs.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).1 ∧
      (extDraw (F := F) (EF := EF) bits).decode (streamCoins (m := m) answer
        (x₀ ++ Fs.witnessInput bits w) acc
        (squeezesFor K (extSamples (EF := EF) bits))) =
        Challenge.toSpec (Fs.smpExt (EF := EF) (idealOf answer)
          (Fs.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).2).1 ∧
      (Fs.smpExt (EF := EF) (idealOf answer)
        (Fs.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).2).2.cap =
        capOf answer (List.replicate (squeezesFor K (extSamples (EF := EF) bits) - 1) [] ++
          (x₀ ++ Fs.witnessInput bits w) :: acc) ∧
      (Fs.smpExt (EF := EF) (idealOf answer)
        (Fs.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).2).2.input = [] := by
  have hd := (Challenge.params EF).d_pos
  have hn := le_squeezesFor_mul (K := K) hK (extSamples (EF := EF) bits)
  cases bits with
  | zero =>
    have hx : x₀ ++ Fs.witnessInput 0 w = x₀ := List.append_nil x₀
    have hs : extSamples (EF := EF) 0 = Challenge.d EF := by simp only [extSamples, ↓reduceIte,
      Nat.add_zero]
    rw [hx]
    rw [hs] at hm hn ⊢
    have hst := sampleStates_succ_eq answer hK x₀ acc (Challenge.d EF - 1)
    rw [Nat.sub_add_cancel hd] at hst
    refine ⟨rfl, ?_, ?_⟩
    · change Fs.extEquiv _ = _
      rw [show Fs.chkWit (idealOf answer) 0 w ⟨capOf answer acc, x₀, []⟩ =
        (true, ⟨capOf answer acc, x₀, []⟩) from rfl, toSpec_smpExt]
      congr 1
      funext j
      rw [Nat.zero_add, sampleAt_streamCoins_eq answer hK hm (by omega)]
    · rw [squeezesFor_sub_one hK hd, Fs.smpExt, smpList_eq]
      exact hst
  | succ b =>
    have hx : Fs.witnessInput (b + 1) w = [w] := rfl
    have hs : extSamples (EF := EF) (b + 1) = Challenge.d EF + 1 := by
      simp only [extSamples, Nat.add_one_ne_zero, ↓reduceIte]
    rw [hx]
    rw [hs] at hm hn ⊢
    have hchk : Fs.chkWit (idealOf answer) (b + 1) w ⟨capOf answer acc, x₀, []⟩ =
        (CompPoly.CanonicalNat.toNat ((idealOf answer).sample
          ⟨capOf answer acc, x₀ ++ [w], []⟩).1 % 2 ^ (b + 1) == 0,
          ((idealOf answer).sample ⟨capOf answer acc, x₀ ++ [w], []⟩).2) := rfl
    have hst := sampleStates_succ_eq answer hK (x₀ ++ [w]) acc (Challenge.d EF)
    rw [hchk]
    refine ⟨?_, ?_, ?_⟩
    · change (powSample _ % 2 ^ (b + 1) == 0) = _
      rw [powSample, sampleAt_streamCoins_eq answer hK hm (by omega)]
      rfl
    · change Fs.extEquiv _ = _
      rw [toSpec_smpExt]
      congr 1
      funext j
      rw [Fs.sampleStates_sample, sampleAt_streamCoins_eq answer hK hm (by omega), Nat.add_comm]
    · rw [squeezesFor_sub_one hK (Nat.succ_pos _), Nat.succ_sub_one, Fs.smpExt, smpList_eq,
        Fs.sampleStates_sample]
      exact hst

/-- **The query draw on the stream.** From the capacity of the blocks `acc` with `x₀` pending,
Plonky3's grinding check passes as the query draw on the coins of the block `x₀` and the witness
accepts, and its query samples are the decoded positions' samples. -/
theorem queryDraw_idealOf (hK : 0 < K) (top t bits : ℕ) (w : F) (x₀ : List F)
    (acc : List (List F)) (hm : squeezesFor K (querySamples t bits) ≤ m) :
    (queryDraw top t bits).accept (streamCoins (m := m) answer (x₀ ++ Fs.witnessInput bits w) acc
        (squeezesFor K (querySamples t bits))) =
        (Fs.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).1 ∧
      ∀ j : Fin t, (queryDraw top t bits).decode (streamCoins (m := m) answer
        (x₀ ++ Fs.witnessInput bits w) acc (squeezesFor K (querySamples t bits))) j =
        positionOf top ((idealOf answer).sample (Fs.sampleStates (idealOf answer)
          (Fs.chkWit (idealOf answer) bits w ⟨capOf answer acc, x₀, []⟩).2 j)).1 := by
  have hn := le_squeezesFor_mul (K := K) hK (querySamples t bits)
  cases bits with
  | zero =>
    have hx : x₀ ++ Fs.witnessInput 0 w = x₀ := List.append_nil x₀
    have hs : querySamples t 0 = t := by simp only [querySamples, ↓reduceIte, Nat.add_zero]
    rw [hx]
    rw [hs] at hm hn ⊢
    refine ⟨rfl, fun j => ?_⟩
    change positionOf top (sampleAt _ j) = _
    rw [sampleAt_streamCoins_eq answer hK hm (by omega)]
    rfl
  | succ b =>
    have hx : Fs.witnessInput (b + 1) w = [w] := rfl
    have hs : querySamples t (b + 1) = t + 1 := by
      simp only [querySamples, Nat.add_one_ne_zero, ↓reduceIte]
    rw [hx]
    rw [hs] at hm hn ⊢
    have hchk : Fs.chkWit (idealOf answer) (b + 1) w ⟨capOf answer acc, x₀, []⟩ =
        (CompPoly.CanonicalNat.toNat ((idealOf answer).sample
          ⟨capOf answer acc, x₀ ++ [w], []⟩).1 % 2 ^ (b + 1) == 0,
          ((idealOf answer).sample ⟨capOf answer acc, x₀ ++ [w], []⟩).2) := rfl
    rw [hchk]
    refine ⟨?_, fun j => ?_⟩
    · change (powSample _ % 2 ^ (b + 1) == 0) = _
      rw [powSample, sampleAt_streamCoins_eq answer hK hm (by omega)]
      rfl
    · change positionOf top (sampleAt _ (1 + j)) = _
      rw [Fs.sampleStates_sample, sampleAt_streamCoins_eq answer hK hm (by omega), Nat.add_comm]

end Draws

/-! ### Observations of a proof -/

section Observations
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- A proof's cap as the cap of a tree of depth `k` with cap height `h`: `none` unless it has the
`2 ^ min h k` digests Plonky3's verifier accepts. -/
def capVec (h k : ℕ) (c : Cap F) : Option (CapOf F h k) :=
  if hc : c.size = 2 ^ min h k then some ⟨c, hc⟩ else none

/-- An extension element in the spec field is observed as its coefficients. -/
theorem extElems_toSpec (x : EF) : extElems (F := F) (Challenge.toSpec x) = Ext.coeffs x := by
  have h : Challenge.toSpec x = Fs.extEquiv fun i => (Challenge.coeffs x).getD i 0 := by
    conv_lhs => rw [← Challenge.ofCoeffs_coeffs x, Challenge.toSpec_ofCoeffs]
    rfl
  rw [h, extElems, Equiv.symm_apply_apply]
  refine List.ext_getElem (by rw [List.length_ofFn, Challenge.length_coeffs]) fun i h1 h2 => ?_
  rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h2]

/-- `n` extension elements read off an array of `n` are observed as the array's coefficients. -/
theorem extsElems_getD {n : ℕ} (a : Array EF) (ha : a.size = n) :
    extsElems (F := F) (fun i : Fin n => Challenge.toSpec (a.getD i 0)) = Fs.coeffs a.toList := by
  have hl : List.ofFn (fun i : Fin n => Challenge.toSpec (a.getD i 0)) =
      a.toList.map Challenge.toSpec := by
    refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, Array.length_toList, ha])
      fun i h1 h2 => ?_
    rw [List.getElem_ofFn, List.getElem_map, Array.getElem_toList,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [ha]; simpa using h1),
      Option.getD_some]
  rw [extsElems, hl, List.flatMap_map, Fs.coeffs]
  congr 1
  funext x
  exact extElems_toSpec x

omit [BaseField F] in
/-- A proof's cap of the accepted size is observed as Plonky3 observes it. -/
theorem capOfElems_of_capVec {h k : ℕ} {c : Cap F} {v : CapOf F h k} (hv : capVec h k c = some v) :
    capOfElems v = capElems c ∧ v.toArray = c := by
  unfold capVec at hv
  split at hv
  · obtain rfl := Option.some.inj hv
    exact ⟨rfl, rfl⟩
  · exact absurd hv (by simp)

omit [BaseField F] in
/-- A cap of `2 ^ min h k` digests is observed as a nonempty list. -/
theorem capOfElems_ne_nil {h k : ℕ} (v : CapOf F h k) : capOfElems v ≠ [] := by
  refine List.ne_nil_of_length_pos ?_
  rw [length_capOfElems]
  exact Nat.mul_pos (by norm_num) (Nat.two_pow_pos _)

end Observations

/-! ### Messages of the snapshot protocol read off a proof -/

section Parse
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.Bcs

/-- The messages after a snapshot move `T`, when a chain block starts. -/
def wrapMsgs {Snap C : Type} [DecidableEq Snap] [SampleableType C] {P : Protocol.{0}}
    {coin : PublicCoin P} {dec : Decoder C coin} (T : Snap) :
    (start : Bool) → Messages PUnit (decoded C coin dec) →
      Messages PUnit
        (decoded C (snapWrapCoin (Snap := Snap) coin start) (snapWrapDecoder dec start))
  | true, msgs => ⟨T, msgs⟩
  | false, msgs => msgs

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable (K m : ℕ) (top d t : ℕ) (P : Fri.Params) (T : (merkleSpec F).QueryCache)
  (finalPoly : Array EF) (queryWitness : F)

/-- FRI's messages of the snapshot protocol read off a proof, every snapshot move `T`: each
committed word's cap from the proof's commitments `cws`, with its grinding witness, after the
first `seed`; then the final polynomial and the query witness; `none` unless the commitments
are one per fold with the caps' sizes. -/
noncomputable def parseFri : {n : ℕ} → (s : Fri.Interaction.Schedule n) → (start : Bool) →
    (seed : List F) → List (Cap F × F) →
    Option (Messages PUnit (decoded (Coins F K m)
      (snapCoin (Fri.Interaction.publicCoin 𝕂 top d t s)
        (friDecoder K m top d t P.commitPowBits P.queryPowBits s)
        (friLayout K m top d t P.commitPowBits P.queryPowBits P.capHeight s seed) start)
      (snapDecoder (Fri.Interaction.publicCoin 𝕂 top d t s)
        (friDecoder K m top d t P.commitPowBits P.queryPowBits s)
        (friLayout K m top d t P.commitPowBits P.queryPowBits P.capHeight s seed) start)))
  | _, .final, start, _, [] => some (wrapMsgs T start
      ⟨fun i => Challenge.toSpec (finalPoly.getD i 0),
        queryWitnessOf top t P.queryPowBits queryWitness, PUnit.unit, PUnit.unit⟩)
  | _, .final, _, _, _ :: _ => none
  | _, .fold .., _, _, [] => none
  | n, .fold k _ _ rest, start, _, cw :: cws =>
      (capVec P.capHeight (n - k) cw.1).bind fun c =>
        (parseFri rest (squeezesFor K (extSamples (EF := EF) P.commitPowBits) != 0) [] cws).map
          fun r => wrapMsgs T start ⟨c, extWitnessOf P.commitPowBits cw.2, PUnit.unit, r⟩

section Wrap
variable {F Snap C : Type} [DecidableEq Snap] [SampleableType C]
  (coins : List F × List (List F) → ℕ → C)

/-- A snapshot move `T` before an oracle node opens it on `T`, as inside a block. -/
theorem openedPath_wrap_oracle {M : Type} [DecidableEq M]
    {interface : OracleInterface.{0, 0} M} {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (@PublicCoin.oracle M _ interface rest next))
    (lay : Layout F Snap (.oracle next) dec) (start : Bool) (T : Snap) (pending tail : List F)
    (acc : List (List F)) (msgs : Messages PUnit (decoded C (snapCoin (.oracle next) dec lay false)
      (snapDecoder (.oracle next) dec lay false))) :
    openedPath coins (.oracle next) dec lay start T pending tail acc (wrapMsgs T start msgs) =
      openedPath coins (.oracle next) dec lay false T pending tail acc msgs := by
  cases start <;> rfl

/-- A snapshot move `T` before a sender node, as inside a block. -/
theorem openedPath_wrap_sender {Moves : Type} {inst : DecidableEq Moves}
    {rest : Moves → Protocol.{0}} (next : (m : Moves) → PublicCoin (rest m))
    (dec : Decoder C (@PublicCoin.sender Moves inst rest next))
    (lay : Layout F Snap (@PublicCoin.sender Moves inst rest next) dec) (start : Bool) (T : Snap)
    (pending tail : List F) (acc : List (List F))
    (msgs : Messages PUnit (decoded C (snapCoin (@PublicCoin.sender Moves inst rest next) dec lay
      false) (snapDecoder (@PublicCoin.sender Moves inst rest next) dec lay false))) :
    openedPath coins (@PublicCoin.sender Moves inst rest next) dec lay start T pending tail acc
        (wrapMsgs T start msgs) =
      openedPath coins (@PublicCoin.sender Moves inst rest next) dec lay false T pending tail acc
        msgs := by
  cases start <;> rfl

end Wrap

end Parse

end CompStark.Fs

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Fs Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (K m : ℕ) (S : Setup EF)
  (T : (merkleSpec F).QueryCache)

/-- The STARK's messages of the snapshot protocol read off a proof, every snapshot move `T`: the
trace's cap, `α`'s (empty) witness, then a snapshot, the quotient's cap and the out-of-domain
witness, a snapshot, the opened values and the batching witness, a snapshot and FRI's messages;
`none` unless the caps have the sizes Plonky3's verifier accepts and the commitments are one per
fold. -/
noncomputable def parse (proof : Proof F EF) :
    Option (Messages PUnit (decoded (Coins F K m) (snapCoin S.publicCoin (S.decoder K m)
      (S.layout K m) false) (snapDecoder S.publicCoin (S.decoder K m) (S.layout K m) false))) :=
  (capVec S.params.capHeight (S.logN + S.params.logBlowup) proof.traceCommit).bind fun tc =>
  (capVec S.params.capHeight (S.logN + S.params.logBlowup) proof.quotientCommit).bind fun qc =>
  (parseFri K m (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen) S.params.numQueries
    S.params T proof.fri.finalPoly proof.fri.queryWitness (S.friSchedule [])
    (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits) != 0) S.friSeed
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)).map fun fri =>
  ⟨tc, extWitnessOf 0 0, PUnit.unit, wrapMsgs T (squeezesFor K (extSamples (EF := EF) 0) != 0)
    ⟨qc, extWitnessOf S.params.oodPowBits proof.oodWitness, PUnit.unit,
      wrapMsgs T (squeezesFor K (extSamples (EF := EF) S.params.oodPowBits) != 0)
        ⟨Fs.openingsOf S proof.opened, extWitnessOf S.params.batchPowBits proof.fri.batchWitness,
          PUnit.unit, fri⟩⟩⟩

end CompStark.Iop.Setup

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Fs Interaction.Oracle Interaction.Oracle.PublicCoin
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF] (K : ℕ)

/-- The statement's input of a verifying key and public values, when the key's commitment is
observed with the statement's length. -/
def inputOf (vk : Option (PreprocessedKey F)) (pis : List F)
    (h : (preprocessedDigest vk).length = C.digestLength) : C.Input :=
  ⟨(preprocessedDigest vk, pis), h⟩

/-- **The selection of a proof.** The messages of the decoded snapshot protocol read off a proof
at the admitted length `n`, every snapshot move `T`: the length, then the STARK's
(`Setup.parse`). -/
noncomputable def parse (T : (merkleSpec F).QueryCache) (n : C.Length) (proof : Proof F EF) :
    Option (Messages PUnit (decoded (Coins F K (C.coinCount EF K))
      (snapCoin (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
        (C.layout EF K (C.coinCount EF K)) true)
      (snapDecoder (C.publicCoin EF) (C.decoder EF K (C.coinCount EF K))
        (C.layout EF K (C.coinCount EF K)) true))) :=
  ((C.setup EF n).parse K (C.coinCount EF K) T proof).map fun msgs => ⟨T, n, msgs⟩

end CompStark.Iop.Statement

/-! ### FRI's path -/

namespace CompStark.Fs
open CompStark.Stark CompStark.RandomOracle CompStark.Fri OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

section FriPath
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}

local notation "𝕂" => Challenge.Spec EF

/-- A path of a FRI fold: the committed word, the folding challenge, and the rest. -/
def foldPath {top d t n k : ℕ} {hk : k ≤ n} {inj : Bool} {rest : Fri.Interaction.Schedule (n - k)}
    (w : Fri.Interaction.Word 𝕂 n) (β : 𝕂)
    (r : (Fri.Interaction.protocol 𝕂 top d t rest).tree.ExecutionPath) :
    (Fri.Interaction.protocol 𝕂 top d t (.fold k hk inj rest)).tree.ExecutionPath :=
  ⟨w, β, r⟩

theorem foldPath_congr {top d t n k : ℕ} {hk : k ≤ n} {inj : Bool}
    {rest : Fri.Interaction.Schedule (n - k)} {w w' : Fri.Interaction.Word 𝕂 n} {β β' : 𝕂}
    {r r' : (Fri.Interaction.protocol 𝕂 top d t rest).tree.ExecutionPath} (hw : w = w')
    (hβ : β = β') (hr : r = r') :
    foldPath (hk := hk) (inj := inj) w β r = foldPath w' β' r' := by
  subst hw hβ hr
  rfl

variable (EF) in
/-- The commit loop's grinding checks pass on the commitments and witnesses `cws`, from the
challenger `s`. -/
def CommitChecks (G : Primitives F Id) (P : Params) : List (Cap F × F) → G.State → Prop
  | [], _ => True
  | cw :: cws, s => (Fs.chkWit G P.commitPowBits cw.2 (Fs.obsList G s (capElems cw.1))).1 = true ∧
      CommitChecks G P cws (Fs.smpExt (EF := EF) G
        (Fs.chkWit G P.commitPowBits cw.2 (Fs.obsList G s (capElems cw.1))).2).2

/-- FRI's path read off one more commitment and folding challenge, one layer later. -/
theorem friPath_cons (cache : MixedMerkleTree.Cache (List F) (Digest F)) (ch : ℕ) (c₀ : Cap F)
    (commits : List (Cap F)) (b₀ : EF) (betas : List EF) {top d t : ℕ} (c : Fin d → 𝕂)
    (xs : Fin t → Fin (2 ^ top)) : ∀ {n : ℕ} (s : Fri.Interaction.Schedule n) (j : ℕ),
    Iop.friPath cache ch (c₀ :: commits) (b₀ :: betas) c xs s (j + 1) =
      Iop.friPath cache ch commits betas c xs s j
  | _, .final, _ => rfl
  | _, .fold _ _ _ rest, j => by
    simp only [Iop.friPath, List.getD_cons_succ, friPath_cons cache ch c₀ commits b₀ betas c xs rest
      (j + 1)]
    rfl

/-- `⌈s / K⌉ ≠ 0` for `s ≠ 0` samples. -/
theorem squeezesFor_ne_zero (hK : 0 < K) {s : ℕ} (hs : 0 < s) : squeezesFor K s ≠ 0 := by
  simp only [squeezesFor]
  exact (Nat.div_pos (by omega) hK).ne'

variable (answer : (q : Query F) → Answer K q) (top d t : ℕ) (P : Params)
  (T : (merkleSpec F).QueryCache) (finalPoly : Array EF) (queryWitness : F)

/-- Plonky3's query check after FRI's commitments `cws` from the challenger `s`. -/
abbrev friQueryCheck (s : Sponge F) (cws : List (Cap F × F)) : Bool × Sponge F :=
  Fs.chkWit (idealOf answer) P.queryPowBits queryWitness (Fs.obsExts (idealOf answer)
    (Fs.commitReplay (EF := EF) (idealOf answer) P cws s).2 finalPoly.toList)

/-- **FRI's draws are Plonky3's.** From the capacity of the completed blocks `acc` with nothing
pending, FRI's messages read off the commitments `cws` (`parseFri`) open, on the coins of their
real chain inputs, to FRI's path read off the proof (`Iop.friPath`): each layer's word under its
commitment, Plonky3's folding challenges, the final polynomial and Plonky3's query positions, when
the grinding checks pass. -/
theorem openedPath_fri (hK : 0 < K)
    (hcm : squeezesFor K (extSamples (EF := EF) P.commitPowBits) ≤ m)
    (hqm : squeezesFor K (querySamples t P.queryPowBits) ≤ m) (hfp : finalPoly.size = d)
    (hd : 0 < d) (ht : 0 < querySamples t P.queryPowBits) :
    ∀ {n : ℕ} (s : Fri.Interaction.Schedule n) (start : Bool) (seed : List F)
    (acc : List (List F)) (st : Sponge F) (cws : List (Cap F × F)) (msgs),
    st.cap = capOf answer acc → st.input = [] →
    parseFri K m top d t P T finalPoly queryWitness s start seed cws = some msgs →
    CommitChecks EF (idealOf answer) P cws (Fs.obsList (idealOf answer) st seed) →
    (friQueryCheck answer P finalPoly queryWitness (Fs.obsList (idealOf answer) st seed)
      cws).1 = true →
    openedPath (fun r n => streamCoins (m := m) answer r.1 r.2 n)
        (Fri.Interaction.publicCoin 𝕂 top d t s)
        (friDecoder K m top d t P.commitPowBits P.queryPowBits s)
        (friLayout K m top d t P.commitPowBits P.queryPowBits P.capHeight s seed) start T [] []
        acc msgs =
      some (Iop.friPath (merkleCache T) P.capHeight (cws.map Prod.fst)
        (Fs.commitReplay (idealOf answer) P cws (Fs.obsList (idealOf answer) st seed)).1
        (fun i => Challenge.toSpec (finalPoly.getD i 0))
        (fun j => positionOf top ((idealOf answer).sample (Fs.sampleStates (idealOf answer)
          (friQueryCheck answer P finalPoly queryWitness (Fs.obsList (idealOf answer) st seed)
            cws).2 j)).1) s 0)
  | _, .final, start, seed, acc, st, [], msgs, hcap, hin, hp, _, hq => by
    obtain rfl := Option.some.inj hp
    have hne : seed ++ Fs.coeffs finalPoly.toList ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (Fs.coeffs_ne_nil (List.ne_nil_of_length_pos
        (by rw [Array.length_toList, hfp]; exact hd)))
    have hobs : Fs.obsExts (idealOf answer)
        (Fs.commitReplay (EF := EF) (idealOf answer) P [] (Fs.obsList (idealOf answer) st seed)).2
        finalPoly.toList = ⟨capOf answer acc, seed ++ Fs.coeffs finalPoly.toList, []⟩ := by
      rw [show Fs.commitReplay (EF := EF) (idealOf answer) P [] (Fs.obsList (idealOf answer) st
        seed) = ([], Fs.obsList (idealOf answer) st seed) from rfl, Fs.obsExts_eq,
        ← Fs.obsList_append, Fs.obsList_idealOf_ne answer _ _ hne, hcap, hin]
      rfl
    obtain ⟨hacc, hdec⟩ := queryDraw_idealOf (m := m) answer hK top t P.queryPowBits queryWitness
      (seed ++ Fs.coeffs finalPoly.toList) acc hqm
    have hx : [] ++ (seed ++ extsElems (fun i : Fin d => Challenge.toSpec (finalPoly.getD i 0))) ++
        [] ++ queryWitnessElems (K := K) (m := m) top t P.queryPowBits
          (queryWitnessOf top t P.queryPowBits queryWitness) =
        seed ++ Fs.coeffs finalPoly.toList ++ Fs.witnessInput P.queryPowBits queryWitness := by
      rw [extsElems_getD _ hfp, queryWitnessElems_queryWitnessOf, List.nil_append,
        List.append_nil]
    have hq' := hq
    simp only [friQueryCheck, hobs] at hq'
    refine (openedPath_wrap_sender _ _ _ _ start T [] [] acc _).trans ?_
    refine (openedPath_sender _ _ _ _ T [] [] acc _ _).trans ?_
    refine (congrArg (Option.map _) (openedPath_challenge _ _ _ _ T _ [] acc _ _ _ _ rfl
      (squeezesFor_ne_zero hK ht) ?_)).trans ?_
    · change (queryDraw top t P.queryPowBits).accept (streamCoins answer ([] ++ (seed ++
        extsElems (fun i : Fin d => Challenge.toSpec (finalPoly.getD i 0))) ++ [] ++
        queryWitnessElems (K := K) (m := m) top t P.queryPowBits
          (queryWitnessOf top t P.queryPowBits queryWitness)) acc
        (squeezesFor K (querySamples t P.queryPowBits))) = true
      rw [hx, hacc, hq']
    · have hxs : (fun j : Fin t => (queryDraw top t P.queryPowBits).decode
          (streamCoins (m := m) answer
          (seed ++ Fs.coeffs finalPoly.toList ++ Fs.witnessInput P.queryPowBits queryWitness) acc
          (squeezesFor K (querySamples t P.queryPowBits))) j) = fun j : Fin t => positionOf top
          ((idealOf answer).sample (Fs.sampleStates (idealOf answer)
            (friQueryCheck answer P finalPoly queryWitness (Fs.obsList (idealOf answer) st seed)
              []).2 j)).1 := funext fun j => by rw [hdec j, friQueryCheck, hobs]
      refine congrArg some ?_
      rw [← hxs, ← hx]
      rfl
  | _, .final, _, _, _, _, _ :: _, _, _, _, hp, _, _ => by simp only [parseFri] at hp; cases hp
  | _, .fold .., _, _, _, _, [], _, _, _, hp, _, _ => by simp only [parseFri] at hp; cases hp
  | n, .fold k hk inj rest, start, seed, acc, st, cw :: cws, msgs, hcap, hin, hp, hchk, hq => by
    simp only [parseFri] at hp
    obtain ⟨c, hc, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hp
    have hco := (capOfElems_of_capVec hc).1
    unfold capVec at hc
    split at hc
    swap
    · exact absurd hc (by simp)
    obtain rfl := Option.some.inj hc
    have hne : capElems cw.1 ≠ [] := hco ▸ capOfElems_ne_nil _
    have hst1 : Fs.obsList (idealOf answer) (Fs.obsList (idealOf answer) st seed) (capElems cw.1) =
        ⟨capOf answer acc, seed ++ capElems cw.1, []⟩ := by
      rw [← Fs.obsList_append, Fs.obsList_idealOf_ne answer _ _
        (List.append_ne_nil_of_right_ne_nil _ hne), hcap, hin]
      rfl
    obtain ⟨hacc, hdec, hcap', hin'⟩ := extDraw_idealOf (m := m) answer hK P.commitPowBits cw.2
      (seed ++ capElems cw.1) acc hcm
    have hx : [] ++ (seed ++ capOfElems (⟨cw.1, by assumption⟩ : CapOf F P.capHeight (n - k))) ++
        [] ++ extWitnessElems (EF := EF) (K := K) (m := m) P.commitPowBits
          (extWitnessOf P.commitPowBits cw.2) =
        seed ++ capElems cw.1 ++ Fs.witnessInput P.commitPowBits cw.2 := by
      rw [extWitnessElems_extWitnessOf, hco, List.nil_append, List.append_nil]
    have hsq := squeezesFor_ne_zero (K := K) hK (s := extSamples (EF := EF) P.commitPowBits)
      (Nat.lt_of_lt_of_le (Challenge.params EF).d_pos (Nat.le_add_right _ _))
    rw [← hst1] at hacc hdec hcap' hin'
    have ih := openedPath_fri hK hcm hqm hfp hd ht rest
      (squeezesFor K (extSamples (EF := EF) P.commitPowBits) != 0) []
      (List.replicate (squeezesFor K (extSamples (EF := EF) P.commitPowBits) - 1) [] ++
        ([] ++ (seed ++ capOfElems (⟨cw.1, by assumption⟩ : CapOf F P.capHeight (n - k))) ++
        [] ++ extWitnessElems (EF := EF) (K := K) (m := m) P.commitPowBits
          (extWitnessOf P.commitPowBits cw.2)) :: acc)
      _ cws r (by rw [hx]; exact hcap') hin' hr hchk.2 hq
    refine (openedPath_wrap_oracle _ _ _ _ start T [] [] acc _).trans ?_
    refine (openedPath_oracle _ _ _ _ T [] [] acc _ _).trans ?_
    refine (congrArg (Option.map _) (openedPath_challenge _ _ _ _ T _ [] acc _ _ _ _ rfl hsq
      ?_)).trans ?_
    · change (extDraw P.commitPowBits).accept (streamCoins answer ([] ++ (seed ++ capOfElems
        (⟨cw.1, by assumption⟩ : CapOf F P.capHeight (n - k))) ++ [] ++
        extWitnessElems (EF := EF) (K := K) (m := m) P.commitPowBits
          (extWitnessOf P.commitPowBits cw.2)) acc
        (squeezesFor K (extSamples (EF := EF) P.commitPowBits))) = true
      rw [hx, hacc]
      exact hchk.1
    · refine (congrArg (Option.map _) (congrArg (Option.map _) ih)).trans ?_
      refine congrArg some (foldPath_congr (EF := EF) (top := top) (d := d) (t := t) (n := n)
        (k := k) (hk := hk) (inj := inj) (rest := rest) ?_ ?_ ?_)
      · rfl
      · change (extDraw P.commitPowBits).decode (streamCoins answer ([] ++ (seed ++ capOfElems
          (⟨cw.1, by assumption⟩ : CapOf F P.capHeight (n - k))) ++ [] ++
          extWitnessElems (EF := EF) (K := K) (m := m) P.commitPowBits
            (extWitnessOf P.commitPowBits cw.2)) acc
          (squeezesFor K (extSamples (EF := EF) P.commitPowBits))) = _
        rw [hx, hdec]
        rfl
      · exact (friPath_cons _ _ _ _ _ _ _ _ rest 0).symm

end FriPath

/-! ### Facts of an accepting run -/

section Accepting
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] (G : Primitives F Id)

/-- An accepting commit loop passes every grinding check. -/
theorem commitChecks_of_loop (P : Params)
    (body : Cap F × F → Array EF → M G (ForInStep (Array EF)))
    (hbody : ∀ cw betas, body cw betas = Fs.commitBody G P cw betas) :
    ∀ (cws : List (Cap F × F)) (betas : Array EF) (s : G.State) (r : Array EF × G.State),
      forIn cws betas body s = .ok r → CommitChecks EF G P cws s
  | [], _, _, _, _ => trivial
  | cw :: cws, betas, s, r, h => by
    obtain ⟨step, st', h1, h2⟩ := Fs.forIn_cons_eq_ok G _ _ _ _ _ _ h
    rw [hbody] at h1
    unfold Fs.commitBody at h1
    rw [observeCap, Fs.bind_ok_of G (Fs.observeList_eq G _ s),
      Fs.bind_ok_of G (Fs.checkWitness_eq G _ _ _)] at h1
    obtain ⟨hc, h1⟩ := Fs.ensure_bind_eq_ok G h1
    rw [Fs.bind_ok_of G (Fs.sampleExt_eq G _)] at h1
    obtain ⟨hs1, hs2⟩ := Prod.mk.inj (Fs.pure_eq_ok G h1)
    subst hs1 hs2
    exact ⟨hc, commitChecks_of_loop P body hbody cws _ _ r h2⟩

/-- **An accepting FRI verifier passes its commit loop's grinding checks**, from the challenger
after FRI's domain separator, on batches whose matrices all have height `2 ^ logMax`. -/
theorem commitChecks_of_verifyFri (P : Params) (proof : FriProof F EF)
    (rounds : List (Round F EF)) (alpha : EF) (logMax : ℕ)
    (hh : ∀ x ∈ rounds, ∀ dp ∈ x.2, dp.1.logSize + P.logBlowup = logMax)
    (s : G.State) (r : Unit × G.State) (h : verifyFri G P proof rounds alpha s = .ok r) :
    CommitChecks EF G P (proof.commits.toList.zip proof.commitWitnesses.toList)
      (Fs.obsList G s (DomainSeparator.friSeed F EF
        (foldSchedule P.maxLogArity (P.logBlowup + P.logFinalPolyLen) logMax [logMax])
        (2 ^ P.logFinalPolyLen) P.commitPowBits P.queryPowBits P.numQueries logMax P.logBlowup
        P.maxLogArity)) := by
  unfold verifyFri at h
  obtain ⟨-, h⟩ := Fs.ensure_bind_eq_ok G h
  obtain ⟨hany, h⟩ := Fs.ensure_bind_eq_ok G h
  have hheights : (((rounds.flatMap (·.2)).map (·.1.logSize + P.logBlowup)).mergeSort
      (fun a b ↦ b ≤ a)).dedup = [logMax] := by
    refine dedup_mergeSort_const _ _ _ (fun x hx ↦ ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨r, hr, hy⟩ := List.mem_flatMap.mp hy
      exact hh r hr y hy
    · simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.isEmpty_eq_false_iff] at hany
      obtain ⟨r, hr, hne⟩ := hany
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
      exact List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨r, hr, hy⟩))
  simp only [hheights, List.headD_cons] at h
  obtain ⟨-, h⟩ := Fs.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Fs.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Fs.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Fs.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Fs.ensure_bind_eq_ok G h
  obtain ⟨-, h⟩ := Fs.ensure_bind_eq_ok G h
  rw [Fs.bind_ok_of G (Fs.observeList_eq G _ s)] at h
  obtain ⟨-, h⟩ := Fs.ensure_bind_eq_ok G h
  obtain ⟨betas, st1, h1, -⟩ := Fs.bind_eq_ok G h
  exact commitChecks_of_loop G P _ (fun _ _ ↦ rfl) _ _ _ _ h1

/-- The claimed values read off a proof of the AIR's shape are observed as Plonky3 observes the
opened values. -/
theorem openingsElems_openingsOf (S : Iop.Setup EF) (o : OpenedValues EF)
    (htl : o.traceLocal.size = S.air.width)
    (htn : (o.traceNext.getD #[]).size = S.air.mainNextWidth)
    (hqc : o.quotientChunks.size = S.chunks)
    (hq4 : ∀ ch ∈ o.quotientChunks, ch.size = Challenge.d EF)
    (hpl : (o.preprocessedLocal.getD #[]).size = S.air.preprocessedWidth)
    (hpn : (o.preprocessedNext.getD #[]).size = S.air.preprocessedNextWidth) :
    S.openingsElems (Fs.openingsOf S o) = Fs.coeffs (Fs.openedValues o) := by
  have hq : (List.ofFn fun c : Fin S.chunks => extsElems (F := F)
      ((Fs.openingsOf S o).quotientAt c)).flatten =
      Fs.coeffs (o.quotientChunks.toList.flatMap (·.toList)) := by
    have hl : (List.ofFn fun c : Fin S.chunks => extsElems (F := F)
        ((Fs.openingsOf S o).quotientAt c)) =
        o.quotientChunks.toList.map fun ch => Fs.coeffs ch.toList := by
      refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, Array.length_toList,
        hqc]) fun i h1 h2 => ?_
      rw [List.getElem_ofFn, List.getElem_map]
      have hi : i < o.quotientChunks.size := by rw [hqc]; simpa using h1
      have hi' : i < o.quotientChunks.toList.length := by rw [Array.length_toList]; exact hi
      have hc : o.quotientChunks.getD i #[] = o.quotientChunks.toList[i]'hi' := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some,
          Array.getElem_toList]
      have h4 := hq4 _ (Array.getElem_mem hi)
      change extsElems (fun e : Fin (Challenge.d EF) =>
        Challenge.toSpec ((o.quotientChunks.getD i #[]).getD e 0)) = _
      rw [extsElems_getD _ (by rw [hc, ← Array.getElem_toList] at *; exact h4), hc]
    rw [hl]
    simp only [Fs.coeffs]
    rw [List.flatMap_assoc, List.flatMap_def]
  have h1 : extsElems (F := F) (Fs.openingsOf S o).traceAt = Fs.coeffs o.traceLocal.toList :=
    extsElems_getD _ htl
  have h2 : extsElems (F := F) (Fs.openingsOf S o).traceNext =
      Fs.coeffs (o.traceNext.getD #[]).toList := extsElems_getD _ htn
  have h3 : extsElems (F := F) (Fs.openingsOf S o).preprocessedAt =
      Fs.coeffs (o.preprocessedLocal.getD #[]).toList := extsElems_getD _ hpl
  have h4 : extsElems (F := F) (Fs.openingsOf S o).preprocessedNext =
      Fs.coeffs (o.preprocessedNext.getD #[]).toList := extsElems_getD _ hpn
  simp only [Iop.Setup.openingsElems, hq, Fs.openedValues, Fs.coeffs_append, h1, h2, h3, h4]

/-- On a proof of the AIR's shape, the PCS's claim counts are the setup's. -/
theorem pcsCounts_eq_of_shape (S : Iop.Setup EF) (vk : Option (PreprocessedKey F))
    (o : OpenedValues EF) (htl : o.traceLocal.size = S.air.width)
    (htn : traceNextOk S.air o = true) (hqc : o.quotientChunks.size = S.chunks)
    (hq4 : ∀ ch ∈ o.quotientChunks, ch.size = Challenge.d EF)
    (hshape : preprocessedShapeOk S.air vk o S.logN = true) :
    Fs.pcsCounts o = Fs.pcsCountsS S := by
  rw [Fs.pcsCounts, Fs.pcsCountsS, (Fs.prep_of_shapeOk hshape).2.2]
  simp only [htl, (traceNext_of_ok htn).2, List.cons_append, List.cons.injEq, List.nil_append,
    and_true, true_and]
  rw [List.eq_replicate_iff, List.length_map, Array.length_toList, hqc]
  refine ⟨rfl, fun b hb ↦ ?_⟩
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hb
  rw [hq4 ch (Array.mem_toList_iff.mp hch)]

end Accepting

end CompStark.Fs

/-! ### The STARK's path -/

namespace CompStark.Fs
open CompStark.Stark

/-- A value mapped inside `Option`, from an equation for the value. -/
theorem map_eq_some_of {α β : Type} {f : α → β} {x : Option α} {a : α} {b : β}
    (hx : x = some a) (hb : f a = b) : x.map f = some b := by
  subst hx
  exact congrArg some hb

/-- A proof's cap parsed at the accepted size is the cap itself. -/
theorem capVec_eq_some {F : Type} {h k : ℕ} {c : Cap F} {v : CapOf F h k}
    (hv : capVec h k c = some v) : ∃ hc : c.size = 2 ^ min h k, v = ⟨c, hc⟩ := by
  unfold capVec at hv
  split at hv
  · exact ⟨_, (Option.some.inj hv).symm⟩
  · exact absurd hv (by simp)

end CompStark.Fs

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Fs CompStark.RandomOracle CompStark.Fri
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {K m : ℕ}

local notation "𝕂" => Challenge.Spec EF

/-- An execution path of the STARK from its messages and challenges. -/
def pathOf (S : Setup EF) (Tm : S.TraceMessage) (α : 𝕂) (Q : S.QuotientMessage) (ζ : 𝕂)
    (o : Openings S) (a : 𝕂) (p : (S.friProtocol []).tree.ExecutionPath) :
    S.protocol.tree.ExecutionPath :=
  ⟨Tm, α, Q, ζ, o, a, p⟩

theorem pathOf_congr (S : Setup EF) {Tm Tm' : S.TraceMessage} {α α' : 𝕂}
    {Q Q' : S.QuotientMessage} {ζ ζ' : 𝕂} {o o' : Openings S} {a a' : 𝕂}
    {p p' : (S.friProtocol []).tree.ExecutionPath} (h1 : Tm = Tm') (h2 : α = α') (h3 : Q = Q')
    (h4 : ζ = ζ') (h5 : o = o') (h6 : a = a') (h7 : p = p') :
    S.pathOf Tm α Q ζ o a p = S.pathOf Tm' α' Q' ζ' o' a' p' := by
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- **Plonky3's verifier draws the STARK's challenges as the snapshot protocol's completion.** If
Plonky3's verifier on the answers `answer` accepts a proof of `2 ^ logN` rows, its messages read off
the proof (`parse`) open, on the coins of their real chain inputs after the STARK's domain
separator, with the statement's elements `preprocessedDigest vk ++ pis` observed at the first
squeeze, to the proof's execution path (`proofPath`) on the hashes of the snapshot `T`. -/
theorem openedPath_parse (S : Setup EF) (answer : (q : Query F) → Answer K q) (hK : 0 < K)
    (hm : squeezesFor K (Challenge.d EF + S.params.numQueries + 1) ≤ m)
    (T : (merkleSpec F).QueryCache) (vk : Option (PreprocessedKey F)) (proof : Proof F EF)
    (pis : List F) (hdb : proof.degreeBits = S.logN)
    (h : verifyWith (idealOf answer) S.params S.air vk proof pis = .ok ())
    (msgs : Messages PUnit (decoded (Coins F K m) (snapCoin S.publicCoin (S.decoder K m)
      (S.layout K m) false) (snapDecoder S.publicCoin (S.decoder K m) (S.layout K m) false)))
    (hp : S.parse K m T proof = some msgs) :
    openedPath (fun r n => streamCoins (m := m) answer r.1 r.2 n) S.publicCoin (S.decoder K m)
        (S.layout K m) false T (starkSeedOf EF S.params S.air S.logN) (preprocessedDigest vk ++ pis)
        [] msgs =
      some (S.proofPath (merkleCache T) (idealOf answer) vk proof pis) := by
  obtain ⟨htl, htn, hqc, hq4, hshape0, -, -, hood, -, hbc, ⟨st, hfriOk⟩, -⟩ :=
    Fs.verifyWith_ok (idealOf answer) S.params S.air vk proof pis h
  have hshape := hshape0
  rw [hdb] at hqc hshape
  have hL : Fs.friLogMax S.params proof = S.logSize := by
    simp only [Fs.friLogMax, hdb, Iop.Setup.logSize]
  have hh : ∀ x ∈ openingRounds S.air vk proof
      (Fs.zetaOf (idealOf answer) S.params S.air vk proof pis),
      ∀ dp ∈ x.2, dp.1.logSize + S.params.logBlowup = S.logSize := by
    intro x hx dp hdp
    rw [← hL]
    simp only [openingRounds, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
      rw [hdp]
    · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hdp
      rfl
    · unfold preprocessedRound at hx
      split at hx
      · rw [List.mem_singleton] at hx
        subst hx
        rw [List.mem_singleton] at hdp
        rw [hdp]
      · exact absurd hx List.not_mem_nil
  obtain ⟨-, -, hcs, hcws, hfp, hw, -, -⟩ :=
    Fs.verifyFri_ok (idealOf answer) S.params proof.fri _ _ _ hh _ _ hfriOk
  have hchecks := commitChecks_of_verifyFri (idealOf answer) S.params proof.fri _ _ _ hh _ _
    hfriOk
  have hnq := (Fs.verifyFri_checks (idealOf answer) S.params proof.fri _ _ _ _ hfriOk).1
  have he (bits : ℕ) : squeezesFor K (extSamples (EF := EF) bits) ≤ m :=
    (squeezesFor_mono ((extSamples_le bits).trans (by omega))).trans hm
  have hqm : squeezesFor K (querySamples S.params.numQueries S.params.queryPowBits) ≤ m :=
    (squeezesFor_mono ((querySamples_le _ _).trans (by omega))).trans hm
  have hd := (Challenge.params EF).d_pos
  -- the parsed messages
  unfold parse at hp
  obtain ⟨tc, htc, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨qc, hqcv, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨fri, hfri, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨-, rfl⟩ := capVec_eq_some htc
  obtain ⟨hqs, rfl⟩ := capVec_eq_some hqcv
  have hqne : capElems proof.quotientCommit ≠ [] :=
    capOfElems_ne_nil (⟨proof.quotientCommit, hqs⟩ : CapOf F S.params.capHeight _)
  -- `α`
  have hα0 : Fs.stateAlpha (idealOf answer) S.params S.air vk proof pis =
      ⟨capOf answer [], starkSeedOf EF S.params S.air S.logN ++ capElems proof.traceCommit ++
        preprocessedDigest vk ++ pis, []⟩ := by
    simp only [Fs.stateAlpha, hdb]
    simp only [Fs.obsList_idealOf_mk, List.nil_append]
    rfl
  obtain ⟨-, hdα, hcα, hiα⟩ := extDraw_idealOf (m := m) answer hK 0 0
    (starkSeedOf EF S.params S.air S.logN ++ capElems proof.traceCommit ++
      preprocessedDigest vk ++ pis) [] (he 0)
  have hcα' : (Fs.smpExt (EF := EF) (idealOf answer) ⟨capOf answer [],
      starkSeedOf EF S.params S.air S.logN ++ capElems proof.traceCommit ++ preprocessedDigest vk ++
        pis, []⟩).2.cap = capOf answer (List.replicate (squeezesFor K (extSamples (EF := EF) 0) - 1)
          [] ++ (starkSeedOf EF S.params S.air S.logN ++ capElems proof.traceCommit ++
            preprocessedDigest vk ++ pis ++ Fs.witnessInput 0 0) :: []) := hcα
  have hiα' : (Fs.smpExt (EF := EF) (idealOf answer) ⟨capOf answer [],
      starkSeedOf EF S.params S.air S.logN ++ capElems proof.traceCommit ++ preprocessedDigest vk ++
        pis, []⟩).2.input = [] := hiα
  -- `ζ`
  set acc₁ := List.replicate (squeezesFor K (extSamples (EF := EF) 0) - 1) [] ++
    (starkSeedOf EF S.params S.air S.logN ++ capElems proof.traceCommit ++ preprocessedDigest vk ++
      pis ++ Fs.witnessInput 0 0) :: [] with hacc₁
  have hζ0 : Fs.obsList (idealOf answer)
      (Fs.smpExt (EF := EF) (idealOf answer) (Fs.stateAlpha (idealOf answer) S.params S.air vk proof
        pis)).2 (capElems proof.quotientCommit) =
      ⟨capOf answer acc₁, capElems proof.quotientCommit, []⟩ := by
    rw [hα0, Fs.obsList_idealOf_ne answer _ _ hqne]
    exact congrArg₂ (fun c i => (⟨c, i, []⟩ : Sponge F)) hcα' (by rw [hiα', List.nil_append])
  obtain ⟨haζ, hdζ, hcζ, hiζ⟩ := extDraw_idealOf (m := m) answer hK S.params.oodPowBits
    proof.oodWitness (capElems proof.quotientCommit) acc₁ (he _)
  have hood' : (Fs.chkWit (idealOf answer) S.params.oodPowBits proof.oodWitness
      ⟨capOf answer acc₁, capElems proof.quotientCommit, []⟩).1 = true := by
    rw [← hζ0]
    exact hood
  -- the batching challenge
  set acc₂ := List.replicate (squeezesFor K (extSamples (EF := EF) S.params.oodPowBits) - 1) [] ++
    (capElems proof.quotientCommit ++ Fs.witnessInput S.params.oodPowBits proof.oodWitness) :: acc₁
    with hacc₂
  have hopen : S.openingsElems (Fs.openingsOf S proof.opened) =
      Fs.coeffs (Fs.openedValues proof.opened) :=
    openingsElems_openingsOf S proof.opened htl (traceNext_of_ok htn).1 hqc hq4
      (Fs.prep_of_shapeOk hshape).1 (Fs.prep_of_shapeOk hshape).2.1
  have hA0 : Fs.pcsState (idealOf answer) S.params
      (openingRounds S.air vk proof (Fs.zetaOf (idealOf answer) S.params S.air vk proof pis))
      (Fs.smpExt (EF := EF) (idealOf answer)
        (Fs.oodCheck (EF := EF) (idealOf answer) S.params S.air vk proof pis).2).2 =
      ⟨capOf answer acc₂, S.pcsSeed ++ S.openingsElems (Fs.openingsOf S proof.opened), []⟩ := by
    rw [Fs.pcsState, Fs.obsOpened_eq, ← Fs.obsList_append,
      Fs.claimCounts_openingRounds S.air vk proof _ htn hshape0,
      Fs.roundValues_openingRounds S.air vk proof _ htn hshape0,
      pcsCounts_eq_of_shape S vk proof.opened htl htn hqc hq4 hshape, hopen,
      Fs.obsList_idealOf_ne answer _ _
        (List.append_ne_nil_of_left_ne_nil (Fs.pcsSeed_ne_nil _ _) _)]
    simp only [Fs.oodCheck]
    rw [hζ0]
    exact congrArg₂ (fun c i => (⟨c, i, []⟩ : Sponge F)) hcζ (by rw [hiζ, List.nil_append]; rfl)
  obtain ⟨haA, hdA, hcA, hiA⟩ := extDraw_idealOf (m := m) answer hK S.params.batchPowBits
    proof.fri.batchWitness (S.pcsSeed ++ S.openingsElems (Fs.openingsOf S proof.opened)) acc₂
    (he _)
  have hbc' : (Fs.chkWit (idealOf answer) S.params.batchPowBits proof.fri.batchWitness
      ⟨capOf answer acc₂, S.pcsSeed ++ S.openingsElems (Fs.openingsOf S proof.opened), []⟩).1 =
      true := by
    rw [← hA0]
    exact hbc
  -- FRI
  set acc₃ := List.replicate (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits) - 1) [] ++
    (S.pcsSeed ++ S.openingsElems (Fs.openingsOf S proof.opened) ++
      Fs.witnessInput S.params.batchPowBits proof.fri.batchWitness) :: acc₂ with hacc₃
  have hsF : Fs.stateFri (idealOf answer) S.params S.air vk proof pis =
      (Fs.smpExt (EF := EF) (idealOf answer) (Fs.chkWit (idealOf answer) S.params.batchPowBits
        proof.fri.batchWitness ⟨capOf answer acc₂, S.pcsSeed ++
          S.openingsElems (Fs.openingsOf S proof.opened), []⟩).2).2 := by
    rw [Fs.stateFri, Fs.batchCheck, hA0]
  have hqpos : 0 < querySamples S.params.numQueries S.params.queryPowBits := by
    simp only [querySamples]
    omega
  have hF := openedPath_fri (m := m) answer (S.logN + S.params.logBlowup)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries S.params T proof.fri.finalPoly
    proof.fri.queryWitness hK (he _) hqm hfp (Nat.two_pow_pos _) hqpos (S.friSchedule [])
    (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits) != 0) S.friSeed acc₃
    (Fs.stateFri (idealOf answer) S.params S.air vk proof pis) _ fri (by rw [hsF]; exact hcA)
    (by rw [hsF]; exact hiA) hfri hchecks hw
  have hsq (bits : ℕ) : squeezesFor K (extSamples (EF := EF) bits) ≠ 0 :=
    squeezesFor_ne_zero hK (Nat.lt_of_lt_of_le hd (Nat.le_add_right _ _))
  refine (openedPath_oracle _ _ _ _ T _ _ [] _ _).trans (map_eq_some_of (a := ?a1) ?r1 ?v1)
  case r1 =>
    refine (openedPath_challenge _ _ _ _ T _ _ [] _ _ _
      (starkSeedOf EF S.params S.air S.logN ++ capElems proof.traceCommit ++
        preprocessedDigest vk ++ pis ++ Fs.witnessInput 0 0) ?hx1 (hsq 0) rfl).trans
      (map_eq_some_of (a := ?a2) ?r2 ?v2)
    case hx1 =>
      change starkSeedOf EF S.params S.air S.logN ++ ([] ++ capElems proof.traceCommit) ++
        (preprocessedDigest vk ++ pis) ++ extWitnessElems (EF := EF) (K := K) (m := m) 0
          (extWitnessOf 0 0) = _
      rw [extWitnessElems_extWitnessOf, List.nil_append, ← List.append_assoc]
    case r2 =>
      refine (openedPath_wrap_oracle _ _ _ _ _ T [] [] _ _).trans
        ((openedPath_oracle _ _ _ _ T [] [] _ _ _).trans (map_eq_some_of (a := ?a3) ?r3 ?v3))
      case r3 =>
        refine (openedPath_challenge _ _ _ _ T _ [] _ _ _ _
          (capElems proof.quotientCommit ++
            Fs.witnessInput S.params.oodPowBits proof.oodWitness) ?hx2 (hsq _) ?ha2).trans
          (map_eq_some_of (a := ?a4) ?r4 ?v4)
        case hx2 =>
          change [] ++ ([] ++ capElems proof.quotientCommit) ++ [] ++
            extWitnessElems (EF := EF) (K := K) (m := m) S.params.oodPowBits
              (extWitnessOf S.params.oodPowBits proof.oodWitness) = _
          rw [extWitnessElems_extWitnessOf, List.nil_append, List.nil_append, List.append_nil]
        case ha2 => exact haζ.trans hood'
        case r4 =>
          refine (openedPath_wrap_sender _ _ _ _ _ T [] [] _ _).trans
            ((openedPath_sender _ _ _ _ T [] [] _ _ _).trans (map_eq_some_of (a := ?a5) ?r5 ?v5))
          case r5 =>
            refine (openedPath_challenge _ _ _ _ T _ [] _ _ _ _
              (S.pcsSeed ++ S.openingsElems (Fs.openingsOf S proof.opened) ++
                Fs.witnessInput S.params.batchPowBits proof.fri.batchWitness) ?hx3 (hsq _)
                ?ha3).trans (map_eq_some_of (a := ?a6) ?r6 ?v6)
            case hx3 =>
              change [] ++ (S.pcsSeed ++ S.openingsElems (Fs.openingsOf S proof.opened)) ++ [] ++
                extWitnessElems (EF := EF) (K := K) (m := m) S.params.batchPowBits
                  (extWitnessOf S.params.batchPowBits proof.fri.batchWitness) = _
              rw [extWitnessElems_extWitnessOf, List.nil_append, List.append_nil]
            case ha3 => exact haA.trans hbc'
            case r6 => exact hF
            case v6 => rfl
          case v5 => rfl
        case v4 => rfl
      case v3 => rfl
    case v2 => rfl
  case v1 =>
    have hseed : S.friSeed = Fs.friSeedOf S.params proof := by
      simp only [friSeed, friArities, Fs.friSeedOf, Fs.friSchedule, Fs.friLogMax, hdb]
    refine S.pathOf_congr rfl ?_ rfl ?_ rfl ?_ ?_
    · refine hdα.trans ?_
      rw [Fs.alphaOf, hα0]
      rfl
    · refine hdζ.trans ?_
      rw [Fs.zetaOf]
      simp only [Fs.oodCheck]
      rw [hζ0]
    · refine hdA.trans ?_
      rw [Fs.batchOf, Fs.batchCheck, hA0]
    · rw [List.map_fst_zip (by rw [Array.length_toList, Array.length_toList, hcs, hcws]), hseed]
      rfl

end CompStark.Iop.Setup

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Fs CompStark.RandomOracle CompStark.Fri OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.PublicCoin Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.Security.HashChain
open Interaction.Oracle.Security.Bcs

variable {F : Type} [BaseField F] (C : Statement F) (EF : Type) [Challenge F EF]

/-- The statement's execution path at the length `n` with the STARK's path there. -/
def pathAt (n : C.Length) (p : (C.setup EF n).protocol.tree.ExecutionPath) :
    (C.protocol EF).tree.ExecutionPath :=
  ⟨n, p⟩

variable {C EF} {K : ℕ}

end CompStark.Iop.Statement

/-! ### The selection exists on an accepted proof -/

namespace CompStark.Fs
open CompStark.Stark CompStark.Fri

section Fits
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

variable (F) in
/-- FRI's commitments fit a schedule: one per fold, each cap of the `2 ^ min h (n - k)` digests
Plonky3's verifier accepts for the tree of the fold from `2 ^ n` points by `2 ^ k`. -/
def CapsFit (h : ℕ) : {n : ℕ} → Fri.Interaction.Schedule n → List (Cap F × F) → Prop
  | _, .final, [] => True
  | _, .final, _ :: _ => False
  | _, .fold .., [] => False
  | n, .fold k _ _ rest, cw :: cws => cw.1.size = 2 ^ min h (n - k) ∧ CapsFit h rest cws

omit [BaseField F] in
/-- Commitments as many as a schedule's folds, each of the size at the height the folds so far
reach, fit the schedule. -/
theorem capsFit_of_sizes (h : ℕ) : ∀ {n : ℕ} (s : Fri.Interaction.Schedule n)
    (cws : List (Cap F × F)), cws.length = (Iop.scheduleArities s).length →
    (∀ i (hi : i < cws.length), cws[i].1.size =
      2 ^ min h (n - ((Iop.scheduleArities s).take (i + 1)).sum)) → CapsFit F h s cws
  | _, .final, [], _, _ => trivial
  | _, .final, _ :: _, hl, _ => absurd hl (by simp [Iop.scheduleArities])
  | _, .fold .., [], hl, _ => absurd hl (by simp [Iop.scheduleArities])
  | n, .fold k _ _ rest, cw :: cws, hl, hs => by
    have h0 := hs 0 (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_zero, Iop.scheduleArities, List.take_succ_cons, List.take_zero,
      List.sum_cons, List.sum_nil, Nat.add_zero] at h0
    refine ⟨h0, capsFit_of_sizes h rest cws
      (by simpa [Iop.scheduleArities] using hl) fun i hi => ?_⟩
    have := hs (i + 1) (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_succ, Iop.scheduleArities, List.take_succ_cons,
      List.sum_cons] at this
    rw [this, Nat.sub_sub]

variable (K m : ℕ) (top d t : ℕ) (P : Params) (T : (merkleSpec F).QueryCache)
  (finalPoly : Array EF) (queryWitness : F)

/-- FRI's messages are read off commitments that fit the schedule. -/
theorem isSome_parseFri : ∀ {n : ℕ} (s : Fri.Interaction.Schedule n) (start : Bool)
    (seed : List F) (cws : List (Cap F × F)), CapsFit F P.capHeight s cws →
    (parseFri K m top d t P T finalPoly queryWitness s start seed cws).isSome = true
  | _, .final, _, _, [], _ => rfl
  | _, .final, _, _, _ :: _, hf => hf.elim
  | _, .fold .., _, _, [], hf => hf.elim
  | n, .fold k _ _ rest, start, seed, cw :: cws, hf => by
    have hr := isSome_parseFri rest (squeezesFor K (extSamples (EF := EF) P.commitPowBits) != 0)
      [] cws hf.2
    simp only [parseFri, capVec, hf.1, ↓reduceDIte, Option.bind_some]
    revert hr
    cases parseFri K m top d t P T finalPoly queryWitness rest
      (squeezesFor K (extSamples (EF := EF) P.commitPowBits) != 0) [] cws
    · exact id
    · exact fun _ => rfl

end Fits

end CompStark.Fs

namespace CompStark.Iop.Setup
open CompStark.Stark CompStark.Fs CompStark.Fri

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

/-- An accepted proof's commitments have the sizes Plonky3's verifier accepts: the trace's and the
quotient's caps of the tree on `L`, and FRI's caps of the folds' trees. -/
theorem caps_of_verifyWith (S : Setup EF) (H : Primitives F Id) (vk : Option (PreprocessedKey F))
    (proof : Proof F EF) (pis : List F) (hdb : proof.degreeBits = S.logN)
    (h : verifyWith H S.params S.air vk proof pis = .ok ()) :
    (∀ k (hk : k < (openingRounds S.air vk proof (Fs.zetaOf H S.params S.air vk proof pis)).length),
      (openingRounds S.air vk proof (Fs.zetaOf H S.params S.air vk proof pis))[k].1.size =
        2 ^ min S.params.capHeight (S.logN + S.params.logBlowup)) ∧
    CapsFit F S.params.capHeight (S.friSchedule [])
      (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨st, hfriOk⟩, -⟩ :=
    Fs.verifyWith_ok H S.params S.air vk proof pis h
  have hL : Fs.friLogMax S.params proof = S.logSize := by
    simp only [Fs.friLogMax, hdb, Iop.Setup.logSize]
  have hh : ∀ x ∈ openingRounds S.air vk proof (Fs.zetaOf H S.params S.air vk proof pis),
      ∀ dp ∈ x.2, dp.1.logSize + S.params.logBlowup = S.logSize := by
    intro x hx dp hdp
    rw [← hL]
    simp only [openingRounds, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
      rw [hdp]
    · obtain ⟨ch, -, rfl⟩ := List.mem_map.mp hdp
      rfl
    · unfold preprocessedRound at hx
      split at hx
      · rw [List.mem_singleton] at hx
        subst hx
        rw [List.mem_singleton] at hdp
        rw [hdp]
      · exact absurd hx List.not_mem_nil
  obtain ⟨-, hfolds, hcs, hcws, -, -, hcrlen, hq⟩ :=
    Fs.verifyFri_ok H S.params proof.fri _ _ _ hh _ _ hfriOk
  have hnq := (Fs.verifyFri_checks H S.params proof.fri _ _ _ _ hfriOk).1
  obtain ⟨hround, hcomm⟩ := Fs.size_caps_of_queryOk H S.params _ _ _ _ _ _ _ _ _ _ _ hcrlen
    (by rw [Array.length_toList, hfolds]) (hq 0 hnq)
  have har : Iop.scheduleArities (S.friSchedule []) = foldSchedule S.params.maxLogArity
      (S.params.logBlowup + S.params.logFinalPolyLen) S.logSize [S.logSize] := by
    rw [friSchedule, Iop.arities_plonky3, Nat.add_comm S.params.logBlowup]
  refine ⟨hround, capsFit_of_sizes _ _ _ ?_ fun i hi => ?_⟩
  · rw [har, List.length_zip, Array.length_toList, Array.length_toList, hcs, hcws, Nat.min_self]
  · have hi' : i < proof.fri.commits.toList.length := by
      rw [List.length_zip] at hi
      omega
    have hc := hcomm i (by rw [Array.length_toList] at hi'; rw [← hcs]; exact hi')
    rw [List.getD_eq_getElem _ _ hi'] at hc
    rw [List.getElem_zip, hc, har]

/-- **An accepted proof has a selection.** Plonky3's verifier on any primitives accepts a proof of
`2 ^ logN` rows only if its messages of the snapshot protocol can be read off it. -/
theorem isSome_parse (S : Setup EF) (K m : ℕ) (T : (merkleSpec F).QueryCache)
    (H : Primitives F Id) (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = S.logN) (h : verifyWith H S.params S.air vk proof pis = .ok ()) :
    (S.parse K m T proof).isSome = true := by
  obtain ⟨hround, hfit⟩ := S.caps_of_verifyWith H vk proof pis hdb h
  have htr := hround 0 (by simp [openingRounds])
  have hqu := hround 1 (by simp [openingRounds])
  simp only [openingRounds, List.cons_append, List.getElem_cons_zero,
    List.getElem_cons_succ] at htr hqu
  have hfri := isSome_parseFri K m (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
    S.params.numQueries S.params T proof.fri.finalPoly proof.fri.queryWitness (S.friSchedule [])
    (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits) != 0) S.friSeed _ hfit
  simp only [parse, capVec, htr, hqu, ↓reduceDIte, Option.bind_some]
  revert hfri
  cases parseFri K m (S.logN + S.params.logBlowup) (2 ^ S.params.logFinalPolyLen)
    S.params.numQueries S.params T proof.fri.finalPoly proof.fri.queryWitness (S.friSchedule [])
    (squeezesFor K (extSamples (EF := EF) S.params.batchPowBits) != 0) S.friSeed
    (proof.fri.commits.toList.zip proof.fri.commitWitnesses.toList)
  · exact id
  · exact fun _ => rfl

end CompStark.Iop.Setup

namespace CompStark.Iop.Statement
open CompStark.Stark CompStark.Fs CompStark.Fri

variable {F : Type} [BaseField F] {C : Statement F} {EF : Type} [Challenge F EF]

/-- **An accepted proof's verifying key is observed with the statement's length.** Plonky3's
verifier on any primitives accepts a proof of an admitted length only if the preprocessed
commitment it observes has the statement's number of elements. -/
theorem length_preprocessedDigest (H : Primitives F Id) (n : C.Length)
    (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = n.1) (h : verifyWith H C.params C.air vk proof pis = .ok ()) :
    (preprocessedDigest vk).length = C.digestLength := by
  obtain ⟨-, -, -, -, hshape, -⟩ := Fs.verifyWith_ok H C.params C.air vk proof pis h
  obtain ⟨hround, -⟩ := (C.setup EF n).caps_of_verifyWith H vk proof pis hdb h
  have hprep := (Fs.prep_of_shapeOk hshape).2.2
  rcases Fs.preprocessedRound_cases C.air vk proof.opened proof.degreeBits hshape
    ⟨1, proof.degreeBits⟩ (Fs.zetaOf H C.params C.air vk proof pis)
    (Fs.zetaOf H C.params C.air vk proof pis * Ext.ofBase (twoAdicGen proof.degreeBits)) with
    ⟨rfl, hl, -, -⟩ | ⟨k, l, rfl, hl, -⟩
  · rw [hl] at hprep
    have hw : C.air.preprocessedWidth = 0 := by
      by_contra hw
      simp only [Option.map_none, Option.toList_none, hw, ↓reduceIte] at hprep
      exact absurd hprep (by simp)
    simp only [preprocessedDigest, List.length_nil, digestLength, hw, ↓reduceIte]
  · rw [hl] at hprep
    have hw : C.air.preprocessedWidth ≠ 0 := by
      intro hw
      simp only [Option.map_some, Option.toList_some, hw, ↓reduceIte] at hprep
      exact absurd hprep (by simp)
    have hn := n.2.preprocessed (Nat.pos_of_ne_zero hw)
    have hk := hround 2 (by simp [openingRounds, preprocessedRound])
    simp only [openingRounds, preprocessedRound, List.cons_append, List.nil_append,
      List.getElem_cons_succ, List.getElem_cons_zero] at hk
    simp only [preprocessedDigest, length_capElems, digestLength, hw, ↓reduceIte, ← hn]
    rw [hk]
    rfl

/-- **An accepted proof has a selection**: Plonky3's verifier on any primitives accepts a proof
of an admitted length only if its messages of the snapshot protocol can be read off it. -/
theorem isSome_parse (K : ℕ) (T : (merkleSpec F).QueryCache) (H : Primitives F Id)
    (n : C.Length) (vk : Option (PreprocessedKey F)) (proof : Proof F EF) (pis : List F)
    (hdb : proof.degreeBits = n.1) (h : verifyWith H C.params C.air vk proof pis = .ok ()) :
    (C.parse EF K T n proof).isSome = true := by
  have hs := (C.setup EF n).isSome_parse K (C.coinCount EF K) T H vk proof pis hdb h
  unfold parse
  revert hs
  cases (C.setup EF n).parse K (C.coinCount EF K) T proof
  · exact id
  · exact fun _ => rfl

end CompStark.Iop.Statement
