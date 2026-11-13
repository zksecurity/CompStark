/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStarkFixtures.TablesKeccak

/-! The compiled `program` and `hashes` systems: the honest non-interactive prover's proofs are
accepted by the executable compiled verifier; proofs with a tampered Merkle root, grinding nonce or
opening row are rejected, and so is the proof of a prover that sends a wrong first table-sumcheck
message and continues honestly, its challenges and nonces consistent with the duplex. -/

set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CompStarkTests.TablesCompiled
open CompStark CompStark.Compiled CompStark.Tables CompStark.BinaryFields CompStark.Keccak
open Interaction Interaction.Oracle Interaction.Oracle.Security

/-- The compiled path type of a presentation. -/
abbrev CompiledPath {original : Protocol} (presentation : Presentation original) : Type :=
  (StandardBcs.compile Commit.Digest presentation.coin).tree.ExecutionPath

/-- Flip a bit of the first Merkle root. -/
def tamperRoot : {original : Protocol} → (presentation : Presentation original) →
    CompiledPath presentation → Option (CompiledPath presentation)
  | _, .refine wire _, path => tamperRoot wire path
  | _, .done, _ => none
  | _, @Presentation.sender _ _ _ _ next, path => (tamperRoot (next path.1) path.2).map (⟨path.1, ·⟩)
  | _, @Presentation.reveal _ _ _ _ _ next, path => (tamperRoot next path.2).map (⟨path.1, ·⟩)
  | _, @Presentation.merkle _ _ _ _ _ _, path =>
      let root : Commit.Digest := path.1
      some ⟨root.set 0 (root[0] ^^^ 1), path.2⟩
  | _, @Presentation.announce _ _ _ _ _ next, path => (tamperRoot (next path.1) path.2).map (⟨path.1, ·⟩)
  | _, .grind _ next, path => (tamperRoot next path.2).map (⟨path.1, ·⟩)
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, path => (tamperRoot next path.2).map (⟨path.1, ·⟩)

/-- Add one to the first grinding nonce. -/
def tamperNonce : {original : Protocol} → (presentation : Presentation original) →
    CompiledPath presentation → Option (CompiledPath presentation)
  | _, .refine wire _, path => tamperNonce wire path
  | _, .done, _ => none
  | _, @Presentation.sender _ _ _ _ next, path => (tamperNonce (next path.1) path.2).map (⟨path.1, ·⟩)
  | _, @Presentation.reveal _ _ _ _ _ next, path => (tamperNonce next path.2).map (⟨path.1, ·⟩)
  | _, @Presentation.merkle _ _ _ _ _ next, path => (tamperNonce next path.2).map (⟨path.1, ·⟩)
  | _, @Presentation.announce _ _ _ _ _ next, path => (tamperNonce (next path.1) path.2).map (⟨path.1, ·⟩)
  | _, .grind _ _, path =>
      let nonce : E := path.1
      some ⟨nonce + 1, path.2⟩
  | _, @Presentation.challenge _ _ _ _ _ _ _ _ next, path => (tamperNonce next path.2).map (⟨path.1, ·⟩)

/-- Add one to the first value of the first opened row. -/
def tamperOpening (openings : Openings) : Option Openings :=
  match openings with
  | ⟨queries, ⟨(x :: row) :: rows, siblings⟩⟩ :: rest => some (⟨queries, ⟨((x + 1) :: row) :: rows, siblings⟩⟩ :: rest)
  | _ => none

/-- A proof with its first root, its first nonce or its first opened value changed. -/
def tamperings {S : System K} {L : Layout S.tables.length} {k M : ℕ} (d : Compiled.Data S L k M)
    (proof : d.Proof) : List (String × Option d.Proof) :=
  let path : CompiledPath d.presentation := proof.2.1
  let attach (tampered : CompiledPath d.presentation) : d.Proof := ⟨proof.1, tampered, proof.2.2⟩
  [("Merkle root", (tamperRoot d.presentation path).map attach),
   ("grinding nonce", (tamperNonce d.presentation path).map attach),
   ("opening row", (tamperOpening proof.2.2).map fun openings => ⟨proof.1, proof.2.1, openings⟩)]

section
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

open CompStark.Tables.Composed CompStark.Multilinear CompStark.Compose

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ}

variable (S L k) in
/-- The honest table rounds, the first message's constant coefficient increased by one. -/
def cheatingRounds (o : Bus.Output S L k) (ξ : E) (w : Witness K S.tables.length) :
    (count : ℕ) → List E → (Compiled.tableRounds S L count).Prover
  | 0, χ => Compiled.tableRoundsProver S L k o ξ w 0 χ
  | count + 1, χ => fun state =>
      let step := Compiled.tableRoundsProver S L k o ξ w (count + 1) χ state
      ((step.1.1 + 1, step.1.2), step.2)

variable (S L k) in
/-- The honest table sumcheck, its first message wrong. -/
def cheatingTable (o : Bus.Output S L k) (w : Witness K S.tables.length) :
    (Compiled.tablePresentation S L).Prover :=
  fun _ ξ => cheatingRounds S L k o ξ w (TableSumcheck.maxHeight S L) []

/-- The honest outer prover with the cheating table sumcheck. -/
def cheatingOuter (d : Compiled.Data S L k M) (external : d.ExternalProver)
    (w : Witness K S.tables.length) (q : Whir.Table K M) : d.outerPresentation.Prover :=
  Presentation.Prover.append _ _
    (Presentation.Prover.append _ _ (Compiled.busProver S L k w) fun busPath =>
      cheatingTable S L k ((Bus.outputClaim S L k busPath).getD rejectedBus) w)
    fun first =>
      let parts := splitPath (Bus.protocol S L k) (TableSumcheck.protocol S L) first
      let bus := (Bus.outputClaim S L k parts.1).getD rejectedBus
      external ((TableSumcheck.outputClaim S L k bus parts.2).getD rejectedOutput) q

/-- The honest compiled prover with the cheating table sumcheck. -/
def cheatingProver (d : Compiled.Data S L k M) (external : d.ExternalProver)
    (w : Witness K S.tables.length) : d.presentation.Prover :=
  let q := Pcs.tableOf M (S.stackValues L M w)
  let word : Whir.oracleMessage K d.evaluated.schedule := wordOfRows (headRowsBase d.evaluated q)
  let cache := Whir.TableCache.ofTable fun u => ofK (q u)
  fun _ => (word, baseRows word, Presentation.Prover.append d.outerPresentation
    (whirPresentation d.evaluated.schedule) (cheatingOuter d external w q) fun outer =>
      whirProver d.evaluated cache.get (openingClaims d.setup (outerOutput d.setup outer)))

end

/-- The cheating prover's compiled proof. -/
def cheatingProve {S : System K} {L : Layout S.tables.length} {k M : ℕ} (d : Compiled.Data S L k M)
    (external : d.ExternalProver) (w : Witness K S.tables.length) : Option d.Proof :=
  match d.presentation.run (cheatingProver d external w) (Transcript.seedDigests d.iv d.statement) with
  | none => none
  | some result => some (d.attachOpenings result.1 result.2)

/-- Accept the honest proof of `w`, and reject its three tamperings and the cheating prover's
proof. -/
def checkSystem {S : System K} {L : Layout S.tables.length} {k M : ℕ} (name : String)
    (d : Compiled.Data S L k M) (external : d.ExternalProver) (w : Witness K S.tables.length) :
    IO Unit := do
  let start ← IO.monoMsNow
  let some proof := d.prove external w | throw (IO.userError s!"{name}: the honest prover failed to grind")
  let proved ← IO.monoMsNow
  unless d.check proof do throw (IO.userError s!"{name}: the honest compiled proof is rejected")
  let checked ← IO.monoMsNow
  for (what, candidate) in tamperings d proof do
    let some bad := candidate | throw (IO.userError s!"{name}: the proof has no {what} to tamper")
    if d.check bad then throw (IO.userError s!"{name}: a tampered {what} is accepted")
  let some cheat := cheatingProve d external w
    | throw (IO.userError s!"{name}: the cheating prover failed to grind")
  if d.check cheat then throw (IO.userError s!"{name}: a wrong table-sumcheck message is accepted")
  IO.println s!"tables (compiled {name}): proved in {proved - start} ms, honest accepted in {checked - proved} ms; tampered root, nonce and opening and a wrong table message rejected"

/-- Run both compiled systems. -/
def check : IO Unit := do
  checkSystem "program" Fixtures.Tables.programData (fun _ _ ↦ PUnit.unit) Examples.programWitness
  checkSystem "hashes" Fixtures.TablesKeccak.hashesData
    (fun o q ↦ Compiled.keccakProver Fixtures.TablesKeccak.keccak o q) Fixtures.TablesKeccak.hashesWitness

end CompStarkTests.TablesCompiled
