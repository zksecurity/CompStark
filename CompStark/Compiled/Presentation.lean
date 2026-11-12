/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Compiled.Projection
public import CompStark.Pcs.RingSwitch.Protocol
public import CompStark.Multilinear.GrandProduct
public import ArkLib.ProofSystem.Whir.Protocol
public import CompStark.Keccak.Commit.Merkle
public import CompStark.Keccak.Transcript.Correspondence

/-! Public-coin presentation of the composed certificate. Coefficient oracles become public
messages, and public rejection is checked by the terminal predicate. Only PCS words remain
oracle messages. A vector challenge consumes its specified sequence of duplex squeezes. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Compiled

open CompStark.BinaryFields CompStark.Multilinear CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp
open scoped ENNReal

section
attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- A fixed number of scalar squeezes and the typed challenge decoded from them. -/
structure Draw (Challenge : Type) where
  /-- Number of consecutive duplex squeezes. -/
  width : ℕ
  /-- Typed interpretation of the squeezed extension-field scalars. -/
  decode : Vector E width → Challenge
  /-- Executable equality for checking the transmitted challenge against the duplex. -/
  equal : DecidableEq Challenge

/-- Consecutive squeezes, retaining their scalar outputs and final state. -/
def squeezeMany : (count : ℕ) → Transcript.State → Vector E count × Transcript.State
  | 0, state => (#v[], state)
  | count + 1, state =>
      let first := Transcript.squeeze state
      let rest := squeezeMany count first.2
      (Vector.ofFn (Fin.cons first.1 (fun i => rest.1[i])), rest.2)

/-- Run the concrete duplex draw for a typed verifier move. -/
def Draw.run {Challenge : Type} (draw : Draw Challenge) (state : Transcript.State) :
    Challenge × Transcript.State :=
  let result := squeezeMany draw.width state
  (draw.decode result.1, result.2)

/-- A scalar challenge consumes exactly one squeeze. -/
def scalarDraw : Draw E := ⟨1, fun scalars => scalars[0], inferInstance⟩

/-- An extension-field vector consumes one squeeze per coordinate in coordinate order. -/
def vectorDraw (width : ℕ) : Draw (Fin width → E) := ⟨width, fun scalars i => scalars[i], inferInstance⟩

/-- The polynomial-basis bit pattern of a squeezed extension-field scalar. -/
def scalarBits (value : E) : ℕ :=
  (value.limb 0).toBitVec.toNat + 2 ^ 64 * (value.limb 1).toBitVec.toNat +
    2 ^ 128 * (value.limb 2).toBitVec.toNat

/-- Merkle query positions are consecutive disjoint bit windows of each 192-bit squeeze,
including windows that cross limb boundaries. Valid setups have column depth between 1 and 64. -/
def queryDraw (queries logColumns : ℕ) : Draw (Fin queries → Fin (2 ^ logColumns)) :=
  let perSqueeze := 192 / logColumns
  { width := (queries + perSqueeze - 1) / perSqueeze
    decode := fun scalars i =>
      let sample := scalars.toArray[i.val / perSqueeze]?.getD 0
      ⟨(scalarBits sample / 2 ^ ((i.val % perSqueeze) * logColumns)) % 2 ^ logColumns,
        Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    equal := inferInstance }

/-- Fixed-width extension-field messages in their authored coordinate order. -/
def fieldEvents {n : ℕ} (values : Fin n → E) : List Transcript.Event :=
  Transcript.scalarEvents (Vector.ofFn values)

/-- A Merkle leaf layout decodes revealed leaves while preserving hidden columns. -/
structure LeafLayout (Messages : Type) where
  /-- Binary tree height. -/
  height : ℕ
  /-- Transmitted base-field words per row. -/
  rowWords : ℕ
  /-- Hashed base-field words per leaf, including the zero prefix. -/
  leafWords : ℕ
  /-- Decode known leaf images, preserving the absence of hidden leaves. -/
  decode : (ℕ → Option (List K)) → Messages

/-- Low-coordinate-first enumeration of a Boolean row. -/
def cubeIndex {n : ℕ} (row : Whir.Cube n) : ℕ :=
  ∑ i : Fin n, if row i then 2 ^ i.val else 0

/-- Decode low-first Boolean coordinates by Horner accumulation. -/
def cubeIndexHorner : {n : Nat} → Whir.Cube n → Nat
  | 0, _ => 0
  | n+1, row => (if row 0 then 1 else 0) + 2 * cubeIndexHorner (fun i : Fin n => row i.succ)
/-- Structural Boolean decoding equals the power-weighted coordinate sum. -/
theorem cubeIndexHorner_eq {n : Nat} (row : Whir.Cube n) : cubeIndexHorner row = cubeIndex row := by
  induction n with
  | zero => simp only [cubeIndexHorner.eq_1, cubeIndex, Fin.sum_univ_zero]
  | succ n ih =>
    rw [cubeIndexHorner.eq_2, ih]
    unfold cubeIndex
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, Nat.pow_zero, Fin.val_succ, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> omega
/-- Decode a bounded Boolean prefix from high to low with a direct coordinate callback. -/
def cubeIndexLoop {n : Nat} (row : Whir.Cube n) : (count : Nat) → count ≤ n → Nat → Nat
  | 0, _, acc => acc
  | count+1, h, acc => cubeIndexLoop row count (by omega)
      (2*acc + if row ⟨count,by omega⟩ then 1 else 0)
/-- Direct prefix decoding retains the weighted bit sum and the shifted incoming accumulator. -/
theorem cubeIndexLoop_eq {n : Nat} (row : Whir.Cube n) (count : Nat) (h : count ≤ n) (acc : Nat) :
    cubeIndexLoop row count h acc =
      (∑ i : Fin count, if row ⟨i.val,by omega⟩ then 2^i.val else 0) + 2^count*acc := by
  induction count generalizing acc with
  | zero => simp only [cubeIndexLoop.eq_1, Fin.sum_univ_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | succ count ih =>
    rw [cubeIndexLoop.eq_2, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, pow_succ]
    split_ifs <;> ring
/-- Decode a complete Boolean index without building a chain of shifted callbacks. -/
def cubeIndexDirect {n : Nat} (row : Whir.Cube n) : Nat := cubeIndexLoop row n (by omega) 0
/-- Direct decoding equals the exact low-first Boolean index. -/
theorem cubeIndexDirect_eq {n : Nat} (row : Whir.Cube n) : cubeIndexDirect row = cubeIndex row := by
  simp only [cubeIndexDirect, cubeIndexLoop_eq, Nat.mul_zero, Nat.add_zero, cubeIndex, Fin.eta]
/-- Compiled leaf decoding traverses Boolean coordinates without materializing summands. -/
@[csimp] theorem cubeIndex_direct : @cubeIndex = @cubeIndexDirect := by
  funext n row
  exact (cubeIndexDirect_eq row).symm

/-- The initial base-field word uses reversed interleaving inside each full leaf. -/
def baseLayout {n : ℕ} (schedule : Whir.Schedule K n) (liveRows : ℕ) : LeafLayout (Whir.oracleMessage K schedule) :=
  { height := match schedule with
      | .last _ tail encoding _ => tail + encoding.rate
      | @Whir.Schedule.more _ tail _ encoding _ _ => tail + encoding.rate
    rowWords := liveRows
    leafWords := 2 ^ schedule.lanes
    decode := fun leaves column =>
      (leaves column.val).map fun payload row =>
        payload.getD (2 ^ schedule.lanes - 1 - cubeIndex row) 0 }

/-- Later extension-field words store forward rows, each as its three polynomial-basis limbs. -/
def extensionLayout {n : ℕ} (schedule : Whir.Schedule K n) :
    LeafLayout (Whir.oracleMessage E schedule) :=
  { height := (baseLayout schedule (2 ^ schedule.lanes)).height
    rowWords := 3 * 2 ^ schedule.lanes
    leafWords := 3 * 2 ^ schedule.lanes
    decode := fun leaves column =>
      (leaves column.val).map fun payload row =>
        let offset := 3 * cubeIndex row
        E.ofLimbs (payload.getD offset 0)
          (payload.getD (offset + 1) 0) (payload.getD (offset + 2) 0) }

/-- A concrete refinement of an authored protocol: reveal short coefficient oracles, retain
Merkle word oracles, and replace rejection-valued challenges by their live uniform branch. -/
inductive Presentation : Protocol → Type 1
  /-- A richer wire protocol is projected causally to the ideal protocol. -/
  | refine {source target : Protocol} (wire : Presentation source)
      (projection : Projection source target) : Presentation target
  /-- The empty continuation. -/
  | done : Presentation .done
  /-- Public prover data retain their typed carrier and event encoding. -/
  | sender {Moves : Type} [DecidableEq Moves] {rest : Moves → Protocol}
      (encode : Moves → List Transcript.Event) (next : (move : Moves) → Presentation (rest move)) :
      Presentation (.public .sender Moves rest)
  /-- A short coefficient oracle is transmitted in full. -/
  | reveal {Messages : Type} [DecidableEq Messages] {interface : OracleInterface Messages}
      {rest : Protocol} (encode : Messages → List Transcript.Event) (next : Presentation rest) :
      Presentation (.oracleWith Messages interface rest)
  /-- A PCS word is replaced by its Keccak root. -/
  | merkle {Messages : Type} [DecidableEq Messages] {interface : OracleInterface Messages}
      {rest : Protocol} (layout : LeafLayout Messages) (next : Presentation rest) :
      Presentation (.oracleWith Messages interface rest)
  /-- Checked prover data are observed and retained by the presentation, then projected away. -/
  | announce {Moves : Type} [DecidableEq Moves] {original : Protocol}
      (encode : Moves → List Transcript.Event) (valid : Moves → Prop)
      (next : Moves → Presentation original) : Presentation original
  /-- A tagged nonce and discarded squeeze precede the next authored move. -/
  | grind {original : Protocol} (bits : ℕ) (next : Presentation original) : Presentation original
  /-- A uniform typed challenge selects the live continuation of the authored protocol. -/
  | challenge {Challenge Moves : Type} [SampleableType Challenge] {rest : Moves → Protocol}
      {tail : Protocol} (move : Challenge → Moves) (shape : ∀ challenge, rest (move challenge) = tail)
      (draw : Draw Challenge) (next : Presentation tail) :
      Presentation (.public .receiver Moves rest)

/-- The normalized IOP keeps only PCS words as oracle moves. -/
def Presentation.protocol : {original : Protocol} → Presentation original → Protocol
  | _, .refine wire _ => wire.protocol
  | _, .done => .done
  | _, @Presentation.sender Moves _ _ _ next =>
      .public .sender Moves fun move => (next move).protocol
  | _, @Presentation.reveal Messages _ _ _ _ next =>
      .public .sender Messages fun _ => next.protocol
  | _, @Presentation.merkle Messages _ interface _ _ next =>
      .oracleWith Messages interface next.protocol
  | _, @Presentation.announce Moves _ _ _ _ next =>
      .public .sender Moves fun move => (next move).protocol
  | _, .grind _ next => .public .sender E fun _ => next.protocol
  | _, @Presentation.challenge Challenge _ _ _ _ _ _ _ next =>
      .public .receiver Challenge fun _ => next.protocol

end
section
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- The normalized tree has a public-coin presentation with challenge-independent shapes. -/
def Presentation.coin : {original : Protocol} → (presentation : Presentation original) →
    PublicCoin presentation.protocol
  | _, .refine wire _ => wire.coin
  | _, .done => .done
  | _, @Presentation.sender _ _ _ _ next => .sender fun move => (next move).coin
  | _, @Presentation.reveal _ _ _ _ _ next => .sender fun _ => next.coin
  | _, @Presentation.merkle _ _ _ _ _ next => .oracle next.coin
  | _, @Presentation.announce _ _ _ _ _ next => .sender fun move => (next move).coin
  | _, .grind _ next => .sender fun _ => next.coin
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next => .challenge next.coin

end

/-- Parse a normalized ideal execution back into the authored composed IOP. -/
def Presentation.originalPath : {original : Protocol} → (presentation : Presentation original) →
    presentation.protocol.tree.ExecutionPath → original.tree.ExecutionPath
  | _, .refine wire projection, path => projection.path (wire.originalPath path)
  | _, .done, _ => PUnit.unit
  | _, @Presentation.sender _ _ _ _ next, path => ⟨path.1, (next path.1).originalPath path.2⟩
  | _, @Presentation.reveal _ _ _ _ _ next, path => ⟨path.1, next.originalPath path.2⟩
  | _, @Presentation.merkle _ _ _ _ _ next, path => ⟨path.1, next.originalPath path.2⟩
  | _, @Presentation.announce _ _ _ _ _ next, path => (next path.1).originalPath path.2
  | _, .grind _ next, path => next.originalPath path.2
  | _, @Presentation.challenge _ _ _ _ _ move shape _ next, path =>
      ⟨move path.1, cast (congrArg (fun protocol : Protocol => protocol.tree.ExecutionPath)
        (shape path.1).symm) (next.originalPath path.2)⟩

/-- Pull back every authored state and backward map along the concrete presentation. -/
def Presentation.extractor : {original : Protocol} → (presentation : Presentation original) →
    {state : KnowledgeState} → RoundExtractor original.tree state →
    RoundExtractor presentation.protocol.tree state
  | _, .refine wire projection, _, extractor => wire.extractor (projection.extractor extractor)
  | _, .done, _, _ => PUnit.unit
  | _, @Presentation.sender _ _ _ _ next, _, extractor => fun move =>
      ⟨(extractor move).1, (extractor move).2.1, (next move).extractor (extractor move).2.2⟩
  | _, @Presentation.reveal _ _ _ _ _ next, _, extractor => fun message =>
      ⟨(extractor message).1, (extractor message).2.1, next.extractor (extractor message).2.2⟩
  | _, @Presentation.merkle _ _ _ _ _ next, _, extractor => fun message =>
      ⟨(extractor message).1, (extractor message).2.1, next.extractor (extractor message).2.2⟩
  | _, @Presentation.announce _ _ _ _ _ next, state, extractor => fun move =>
      ⟨state, id, (next move).extractor extractor⟩
  | _, .grind _ next, state, extractor => fun _ => ⟨state, id, next.extractor extractor⟩
  | _, @Presentation.challenge _ _ _ _ _ move shape _ next, _, extractor => fun challenge =>
      ⟨(extractor (move challenge)).1, (extractor (move challenge)).2.1,
        next.extractor (shape challenge ▸ (extractor (move challenge)).2.2)⟩

/-- Protocol equality transports the terminal state along its path cast. -/
theorem terminalState_transport {first second : Protocol} (equal : first = second)
    {state : KnowledgeState} (extractor : RoundExtractor first.tree state)
    (path : second.tree.ExecutionPath) :
    (equal ▸ extractor).terminalState path = extractor.terminalState
      (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath) equal.symm) path) := by
  subst second
  rfl

/-- Protocol equality transports extraction and the corresponding terminal witness together. -/
theorem extractWitness_transport {first second : Protocol} (equal : first = second)
    {state : KnowledgeState} (extractor : RoundExtractor first.tree state)
    (path : second.tree.ExecutionPath)
    (witness : ((equal ▸ extractor).terminalState path).Witness) :
    (equal ▸ extractor).extractWitness path witness = extractor.extractWitness
      (cast (congrArg (fun p : Protocol => p.tree.ExecutionPath) equal.symm) path)
      (terminalState_transport equal extractor path ▸ witness) := by
  subst second
  rfl

/-- Protocol equality preserves the prover implications. -/
theorem prover_preserving_transport {first second : Protocol} (equal : first = second)
    {state : KnowledgeState} (extractor : RoundExtractor first.tree state)
    (preserving : extractor.IsProverPreserving first.roles) :
    (equal ▸ extractor).IsProverPreserving second.roles := by
  subst second
  exact preserving

/-- Pulled-back terminal states are the authored states on the parsed execution. -/
theorem Presentation.terminalState_eq {original : Protocol} (presentation : Presentation original)
    {state : KnowledgeState} (extractor : RoundExtractor original.tree state)
    (path : presentation.protocol.tree.ExecutionPath) :
    (presentation.extractor extractor).terminalState path =
      extractor.terminalState (presentation.originalPath path) := by
  induction presentation generalizing state with
  | refine wire projection ih =>
      exact (ih (projection.extractor extractor) path).trans (projection.terminalState_eq extractor _)
  | done => rfl
  | sender encode next ih => exact ih path.1 (extractor path.1).2.2 path.2
  | reveal encode next ih => exact ih (extractor path.1).2.2 path.2
  | merkle layout next ih => exact ih (extractor path.1).2.2 path.2
  | announce encode valid next ih => exact ih path.1 extractor path.2
  | grind bits next ih => exact ih extractor path.2
  | challenge move shape draw next ih =>
      exact (ih _ path.2).trans
        (terminalState_transport (shape path.1) (extractor (move path.1)).2.2 _)

/-- Complete pullback extraction uses exactly the composed certificate's backward maps. -/
theorem Presentation.extractWitness_eq {original : Protocol} (presentation : Presentation original)
    {state : KnowledgeState} (extractor : RoundExtractor original.tree state)
    (path : presentation.protocol.tree.ExecutionPath)
    (witness : ((presentation.extractor extractor).terminalState path).Witness) :
    (presentation.extractor extractor).extractWitness path witness =
      extractor.extractWitness (presentation.originalPath path)
        (presentation.terminalState_eq extractor path ▸ witness) := by
  induction presentation generalizing state with
  | refine wire projection ih =>
      have first := ih (projection.extractor extractor) path witness
      have second := projection.extractWitness_eq extractor (wire.originalPath path)
        (wire.terminalState_eq (projection.extractor extractor) path ▸ witness)
      convert first.trans second using 1
      · rfl
      · apply congrArg (extractor.extractWitness (projection.path (wire.originalPath path)))
        exact eq_of_heq ((eqRec_heq _ _).trans
          ((eqRec_heq _ _).trans (eqRec_heq _ _)).symm)
  | done => rfl
  | sender encode next ih =>
      exact congrArg (extractor path.1).2.1 (ih path.1 (extractor path.1).2.2 path.2 witness)
  | reveal encode next ih =>
      exact congrArg (extractor path.1).2.1 (ih (extractor path.1).2.2 path.2 witness)
  | merkle layout next ih =>
      exact congrArg (extractor path.1).2.1 (ih (extractor path.1).2.2 path.2 witness)
  | announce encode valid next ih => exact ih path.1 extractor path.2 witness
  | grind bits next ih => exact ih extractor path.2 witness
  | challenge move shape draw next ih =>
      have first := ih _ path.2 witness
      have second := extractWitness_transport (shape path.1) (extractor (move path.1)).2.2
        (next.originalPath path.2) ((next.terminalState_eq _ path.2) ▸ witness)
      have joined := congrArg (extractor (move path.1)).2.1 (first.trans second)
      convert joined using 1
      · rfl
      · apply congrArg (extractor (move path.1)).2.1
        apply congrArg (RoundExtractor.extractWitness (extractor (move path.1)).2.2 _)
        exact eq_of_heq ((eqRec_heq _ _).trans
          ((eqRec_heq _ _).trans (eqRec_heq _ _)).symm)

/-- A normalized certificate uses uniform public challenges and the unit upper bound for each
local escape. Standard-model soundness uses the exact CI events rather than these budgets. -/
noncomputable def uniformChallenges : {protocol : Protocol} → (coin : PublicCoin protocol) →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles
  | _, .done => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next => ⟨PUnit.unit, fun move => uniformChallenges (next move)⟩
  | _, @PublicCoin.oracle _ _ _ _ next => fun _ => uniformChallenges next
  | _, @PublicCoin.challenge Challenge _ _ next =>
      ⟨⟨$ᵗ Challenge, 1⟩, fun _ => uniformChallenges next⟩

/-- Pulling back a presentation preserves each prover knowledge implication. -/
theorem Presentation.prover_preserving : {original : Protocol} →
    (presentation : Presentation original) → {state : KnowledgeState} →
    (extractor : RoundExtractor original.tree state) →
    extractor.IsProverPreserving original.roles →
    (presentation.extractor extractor).IsProverPreserving presentation.protocol.roles
  | _, .refine wire projection, _, extractor, preserving =>
      wire.prover_preserving _ (projection.prover_preserving extractor preserving)
  | _, .done, _, _, _ => trivial
  | _, @Presentation.sender _ _ _ _ next, _, extractor, preserving =>
      ⟨preserving.1, fun move => (next move).prover_preserving _ (preserving.2 move)⟩
  | _, @Presentation.reveal _ _ _ _ _ next, _, extractor, preserving =>
      ⟨fun message _ => preserving.1 message, fun message =>
        next.prover_preserving _ (preserving.2 message)⟩
  | _, @Presentation.merkle _ _ _ _ _ next, _, extractor, preserving =>
      ⟨preserving.1, fun message => next.prover_preserving _ (preserving.2 message)⟩
  | _, @Presentation.announce _ _ _ _ _ next, _, extractor, preserving =>
      ⟨fun _ _ _ known => known, fun move => (next move).prover_preserving extractor preserving⟩
  | _, .grind _ next, _, extractor, preserving =>
      ⟨fun _ _ _ known => known, fun _ => next.prover_preserving extractor preserving⟩
  | _, @Presentation.challenge _ _ _ _ _ move shape _ next, _, extractor, preserving => by
      constructor
      · intro challenge impossible
        cases impossible
      · intro challenge
        exact next.prover_preserving _
          (prover_preserving_transport (shape challenge) _ (preserving.2 (move challenge)))

/-- The probability of each uniform local escape is at most one. -/
theorem uniformChallenges_bound : {protocol : Protocol} → (coin : PublicCoin protocol) →
    {state : KnowledgeState} → (extractor : RoundExtractor protocol.tree state) →
    extractor.IsLocallyBounded protocol.roles (uniformChallenges coin)
  | _, .done, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, _, extractor => fun move =>
      uniformChallenges_bound (next move) (extractor move).2.2
  | _, @PublicCoin.oracle _ _ _ _ next, _, extractor => fun message =>
      uniformChallenges_bound next (extractor message).2.2
  | _, @PublicCoin.challenge _ _ _ next, _, extractor => by
      refine ⟨?_, fun challenge => uniformChallenges_bound next (extractor challenge).2.2⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro round context
      exact prEvent_le_one _

/-- Normalization preserves prover knowledge and bounds every uniform local escape by one. -/
noncomputable def Presentation.certificate {original : Protocol} (presentation : Presentation original)
    {state : KnowledgeState} (certificate : KnowledgeCertificate original.tree original.roles state) :
    KnowledgeCertificate presentation.protocol.tree presentation.protocol.roles state where
  extractor := presentation.extractor certificate.extractor
  challenges := uniformChallenges presentation.coin
  prover_preserving := presentation.prover_preserving _ certificate.prover_preserving
  local_bound := uniformChallenges_bound presentation.coin _

/-- Presentations compose along the same constant-shape append as the authored certificates. -/
def Presentation.append {first second : Protocol} (presentation : Presentation first)
    (suffix : Presentation second) : Presentation (Compose.appendProtocol first second) :=
  match presentation with
  | .refine wire projection => .refine (wire.append suffix) (projection.append second)
  | .done => suffix
  | @Presentation.sender Moves _ _ encode next =>
      @Presentation.sender Moves _ _ encode fun move => (next move).append suffix
  | @Presentation.reveal Messages _ interface _ encode next => .reveal encode (next.append suffix)
  | @Presentation.merkle Messages _ interface _ layout next => .merkle layout (next.append suffix)
  | @Presentation.announce Moves _ _ encode valid next =>
      @Presentation.announce Moves _ _ encode valid fun move => (next move).append suffix
  | .grind bits next => .grind bits (next.append suffix)
  | @Presentation.challenge Challenge Moves _ rest tail move shape draw next =>
      @Presentation.challenge Challenge Moves _
        (fun move => Compose.appendProtocol (rest move) second) (Compose.appendProtocol tail second)
        move (fun challenge =>
          congrArg (fun first => Compose.appendProtocol first second) (shape challenge))
        draw (next.append suffix)

section
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- Reveal the positive-degree cofactor tail and draw the next normalized coordinate. -/
def grandRounds (degree : ℕ) {tail : Protocol} (suffix : Presentation tail) :
    (count : ℕ) → Presentation (GrandProduct.roundsProtocol degree tail count)
  | 0 => suffix
  | count + 1 => .reveal (fun message : GrandProduct.Message degree => fieldEvents message)
      (.challenge some (fun _ => rfl) scalarDraw (grandRounds degree suffix count))

/-- A bus round absorbs exactly its cofactor degree many scalars, without the constant. -/
theorem grandRounds_message_width (degree : ℕ) (message : GrandProduct.Message degree) :
    (fieldEvents message).length = degree := by
  simp only [fieldEvents, Transcript.scalarEvents, List.length_map, Vector.length_toList]


/-- Child interpolation uses one scalar per coordinate. -/
def interpolation {tail : Protocol} (suffix : Presentation tail) :
    (count : ℕ) → Presentation (GrandProduct.interpolationProtocol tail count)
  | 0 => suffix
  | count + 1 => .challenge id (fun _ => rfl) scalarDraw (interpolation suffix count)

/-- The product-tree presentation reveals all short coefficient and child-value messages. -/
def grandProduct {tail : Protocol} (suffix : Presentation tail) :
    (layers : List ℕ) → (used : ℕ) → Presentation (GrandProduct.protocol tail layers used)
  | [], _ => suffix
  | lanes :: rest, used => .challenge id (fun _ => rfl) scalarDraw
      (grandRounds (2 ^ lanes)
        (.sender (fun values => fieldEvents fun i : Fin (3 * 2 ^ lanes) =>
          values ⟨i.val / 2 ^ lanes, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr i.isLt⟩
            ⟨i.val % 2 ^ lanes, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
          (fun _ => interpolation (grandProduct suffix rest (used + lanes)) lanes)) used)

/-- The scalar-only ring switch has no prover messages. -/
def ringPresentation : (count : ℕ) → Presentation (Pcs.RingSwitch.draws count)
  | 0 => .done
  | count + 1 => .challenge id (fun _ => rfl) scalarDraw (ringPresentation count)

/-- WHIR scalar sumcheck rounds transmit the constant and quadratic coefficients. -/
def whirRounds {tail : Protocol} (suffix : Presentation tail) :
    (count : ℕ) → Presentation (Whir.scalarRounds E count tail)
  | 0 => suffix
  | count + 1 => .sender (fun message => fieldEvents ![message.1, message.2 0]) fun _ =>
      .challenge id (fun _ => rfl) scalarDraw (whirRounds suffix count)

end
end CompStark.Compiled
