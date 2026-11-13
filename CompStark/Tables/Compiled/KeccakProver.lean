/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Tables.Compiled.Prover
public import CompStark.Tables.Compiled.External
public import CompStark.Keccak.GkrProver.Refinement
public import CompStark.Keccak.Transcript.Native

/-! The Keccak table's argument's prover for the compiled system: at the GKR's first move it seeds
the native Keccak-f GKR prover's writer with the duplex state, runs it on the stack's slot region
at the table's point, and sends the native transcript's messages; ring switching sends nothing. -/

set_option Elab.async false
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

@[expose] public section

namespace CompStark.Tables.Compiled

open CompStark.Stark CompStark.BinaryFields CompStark.Multilinear CompStark.Tables.System
open CompStark.Compiled CompStark.Tables.Composed CompStark.Keccak CompStark.Compose
open _root_.Interaction _root_.Interaction.Oracle _root_.Interaction.Oracle.Security

attribute [local instance 3000] Pcs.RingSwitch.sampleableE Pcs.RingSwitch.sampleableK

/-- The GKR's messages read off a history in which every message and challenge has one entry. -/
def listProver : (steps : List Keccak.Gkr.WireStep) → List (List E) → (gkrPresentation steps).Prover
  | [], _ => PUnit.unit
  | .message _ :: rest, history => fun _ =>
      ⟨fun i => (history.headD []).getD i.val 0, listProver rest history.tail⟩
  | .challenge _ :: rest, history => fun _ _ => listProver rest history.tail

/-- A GKR prover chosen from the duplex state at its first move. -/
def statefulProver : (steps : List Keccak.Gkr.WireStep) →
    (Transcript.State → (gkrPresentation steps).Prover) → (gkrPresentation steps).Prover
  | [], _ => PUnit.unit
  | .message _ :: _, prover => fun state => prover state state
  | .challenge _ :: _, prover => fun state => prover state state

/-- Ring switching sends nothing. -/
def ringProver : (count : ℕ) → (ringPresentation count).Prover
  | 0 => PUnit.unit
  | count + 1 => fun _ _ => ringProver count

variable {S : System K} {L : Layout S.tables.length} {k M : ℕ} (kt : KeccakTable S L M)

/-- The native Keccak-f GKR transcript on the slot region at the table's point, its writer seeded
with a duplex state. -/
def nativeTranscript (state : Transcript.State) (o : TableSumcheck.Output S L k) (q : Whir.Table K M) :
    Keccak.Gkr.Transcript E kt.p :=
  let committed := Array.ofFn fun u : Fin (2 ^ (kt.p + 10)) => UInt64.ofBitVec (kt.word q u).toBitVec
  let batch := Array.ofFn fun i : Fin (kt.p + 4) => BF64.WordExt3.ofField (kt.instancePoint o i)
  let output := Array.ofFn fun l : Fin 25 =>
    BF64.WordExt3.ofField (o.values ⟨kt.table, kt.active⟩ (kt.outputIndex l))
  let writer : Keccak.GkrProver.Writer := { state := TranscriptDuplex.duplexState state }
  let reduction := Keccak.GkrProver.prove writer
    (Keccak.GkrProver.buildWitness (kt.p + 4) committed) committed batch output
  reduction.toProtocol kt.p (Keccak.GkrProver.prove_layers_size ..)

/-- The Keccak table's argument's prover: the native GKR seeded at its first move, then ring
switching. -/
def keccakProver (o : TableSumcheck.Output S L k) (q : Whir.Table K M) : (keccakPresentation kt).Prover :=
  Presentation.Prover.append _ _
    (statefulProver (gkrSteps kt.p) fun state =>
      listProver (gkrSteps kt.p)
        ((Keccak.Gkr.transcriptMessages (nativeTranscript kt state o q)).drop (kt.p + 4)))
    fun _ => ringProver 6

end CompStark.Tables.Compiled
