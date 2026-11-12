/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.WireEncoding
public import CompStark.Keccak.Gkr.OpeningExecution
public import CompStark.Keccak.Gkr.InitialSampling

/-! # Typed execution of the exact public GKR wire schedule -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
open OracleComp
open scoped BigOperators ENNReal
namespace CompStark.Keccak.Gkr

/-- A singleton coefficient vector is encoded as its sole scalar. -/
theorem ofFn_one {E : Type} (a : Fin 1 → E) : List.ofFn a = [a 0] := rfl

/-- The transcript header retained after the initial coordinates and middle value. -/
def header {E : Type} [Zero E] {p : Nat} (r : Fin (p+10) → E) (middle : E) : Transcript E p where
  instancePoint := fun i => r ⟨i.val,by omega⟩
  segment := r ⟨p+4,by omega⟩
  lanePoint := fun i => r ⟨p+5+i.val,by omega⟩
  middleValue := middle
  layers := fun _ => ⟨0,0,0,0,0,0,0,0⟩
  openings := ⟨0,0,0,0,0,0⟩

/-- Flattening a sampled header recovers its actual coordinate vector. -/
theorem initialPoint_header {E : Type} [Zero E] {p : Nat} (r : Fin (p+10) → E) (middle : E) :
    initialPoint (header r middle) = r := by
  funext i
  unfold initialPoint header
  split
  · rfl
  · split
    · rename_i hi
      exact congrArg r (Fin.ext hi.symm)
    · change r ⟨p+5+(i.val-(p+5)),by omega⟩ = r i
      congr 1
      apply Fin.ext
      dsimp only
      omega

/-- The initial challenge kinds in their source order. -/
def startKinds (p : Nat) : List Challenge :=
  (List.range (p+4)).map .initialInstance ++ [.segment] ++ (List.range 5).map .lane

/-- The initial adapter draws exactly `p+10` coordinates. -/
theorem startKinds_length (p : Nat) : (startKinds p).length = p+10 := by
  simp only [startKinds,List.length_append,List.length_map,List.length_range,List.length_cons,List.length_nil]

/-- Challenge-only blocks have the coordinate sampler's distribution, independently of their tags. -/
theorem runWire_onlyChallenges {E : Type} [Fintype E] [Nonempty E]
    (prover : Prover E) (kinds : List Challenge) (history : List (List E)) :
    runWire E prover (kinds.map .challenge) history =
      coordinateMessages <$> runCoordinates E kinds.length := by
  induction kinds generalizing history with
  | nil => simp only [List.map_nil,runWire,List.length_nil,runCoordinates,map_pure,
      coordinateMessages,List.ofFn_zero]
  | cons kind rest ih =>
    simp only [List.map_cons,runWire,List.length_cons,runCoordinates,map_eq_bind_pure_comp,
      Function.comp_def,bind_assoc,pure_bind]
    congr 1
    funext r
    rw [ih]
    simp only [map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind,
      coordinateMessages,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]

/-- Coordinate encodings split at an explicit dimension boundary. -/
theorem coordinateMessages_blocks {E : Type} {n a b : Nat} (h : n=a+b) (r : Fin n → E) :
    coordinateMessages r = coordinateMessages (fun i : Fin a => r ⟨i.val,by omega⟩) ++
      coordinateMessages (fun i : Fin b => r ⟨a+i.val,by omega⟩) := by
  subst n
  exact List.ofFn_add

/-- The initial header messages are exactly the sampled coordinate vector in wire order. -/
theorem header_messages {E : Type} [Zero E] {p : Nat} (r : Fin (p+10) → E) (middle : E) :
    (List.ofFn fun i => [(header r middle).instancePoint i]) ++ [[(header r middle).segment]] ++
      (List.ofFn fun i => [(header r middle).lanePoint i]) = coordinateMessages r := by
  rw [coordinateMessages_blocks (a := p+4) (b := 6) (by omega)]
  simp only [coordinateMessages,List.ofFn_succ,header,Fin.val_zero,Nat.add_zero,Fin.val_succ,List.append_assoc]
  congr 2

/-- Sumcheck tags only label the local loss and do not alter the sampled wire distribution. -/
theorem runWire_rounds_tags {E : Type} [Fintype E] [Nonempty E] (prover : Prover E)
    (n d : Nat) (kind other : Nat → Challenge) (history : List (List E)) :
    runWire E prover (roundSteps n d kind) history = runWire E prover (roundSteps n d other) history := by
  rw [← runSumcheck_encoding,← runSumcheck_encoding]

/-- Splitting a sumcheck block preserves its ordered message/challenge schedule. -/
theorem roundSteps_add (n m d : Nat) (kind : Nat → Challenge) :
    roundSteps (n+m) d kind = roundSteps n d kind ++ roundSteps m d (fun i => kind (n+i)) := by
  simp only [roundSteps,List.range_add,List.flatMap_append,List.flatMap_map]

/-- Bit-slice opening messages, including the final vector of 64 values. -/
def inputOpeningMessages {E : Type} (o : OpeningTranscript E) : List (List E) :=
  roundMessages o.inputPolys o.inputPoint ++ [List.ofFn o.slices]

/-- All messages in the two committed-table openings. -/
def openingMessages {E : Type} (o : OpeningTranscript E) : List (List E) :=
  roundMessages o.outputPolys o.outputPoint ++ [[o.outputValue]] ++ inputOpeningMessages o

/-- The typed input-opening sampler executes exactly its concrete wire block. -/
theorem runInputOpening_encoding {E : Type} [Fintype E] [Nonempty E]
    (prover : Prover E) (history : List (List E)) (base : OpeningTranscript E) :
    inputOpeningMessages <$> runInputOpening E prover history base =
      runWire E prover (roundSteps 4 1 .inputLow ++ roundSteps 6 1 .inputSlot ++ [.message 64]) history := by
  have he : runWire E prover (roundSteps 4 1 .inputLow ++ roundSteps 6 1 .inputSlot) history =
      runWire E prover (roundSteps 10 1 .inputLow) history := by
    rw [show 10=4+6 by omega,roundSteps_add,runWire_append,runWire_append]
    congr 1
  rw [runWire_append,he,← runSumcheck_encoding]
  simp only [runInputOpening,inputOpeningMessages,map_eq_bind_pure_comp,Function.comp_def,
    bind_assoc,pure_bind,runWire]

/-- The typed opening sampler executes the exact word and bit-slice wire blocks. -/
theorem runOpenings_encoding {E : Type} [Fintype E] [Nonempty E] [Zero E]
    (prover : Prover E) (history : List (List E)) :
    openingMessages <$> runOpenings E prover history =
      runWire E prover (roundSteps 6 1 .outputSlot ++ [.message 1] ++
        roundSteps 4 1 .inputLow ++ roundSteps 6 1 .inputSlot ++ [.message 64]) history := by
  have hi (history : List (List E)) :
      runWire E prover (roundSteps 4 1 .inputLow ++ (roundSteps 6 1 .inputSlot ++ [.message 64])) history =
        (do let trace ← runSumcheck E prover 1 10 history
            pure (roundMessages trace.1 trace.2 ++ [List.ofFn (prover (history ++ roundMessages trace.1 trace.2) 64)])) := by
    have h := (runInputOpening_encoding prover history (⟨0,0,0,0,0,0⟩ : OpeningTranscript E)).symm
    simpa only [List.append_assoc,runInputOpening,inputOpeningMessages,Functor.map_map,Function.comp_def,
      map_eq_bind_pure_comp,bind_assoc,pure_bind] using h
  simp only [List.append_assoc]
  rw [runWire_append,← runSumcheck_encoding]
  simp only [map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind,List.cons_append,List.nil_append,runWire]
  simp_rw [hi]
  simp only [runOpenings,runInputOpening,openingMessages,inputOpeningMessages,map_eq_bind_pure_comp,
    Function.comp_def,bind_assoc,pure_bind,List.append_assoc,List.singleton_append,ofFn_one]

/-- Execute all layers and openings after the fixed sampled header. -/
noncomputable def runAfterHeader (E : Type) [Fintype E] [Nonempty E] [Zero E] {p : Nat}
    (prover : Prover E) (history : List (List E)) (base : Transcript E p) : ProbComp (Transcript E p) := do
  let ts ← runLayerSequence E p prover 12 history
  let o ← runOpenings E prover (history ++ sequenceMessages ts)
  pure {base with layers := ts, openings := o}

/-- Execute the full GKR protocol with the initial challenges preceding the first prover value. -/
noncomputable def runProtocol (E : Type) [Fintype E] [Nonempty E] [Zero E] (p : Nat)
    (prover : Prover E) : ProbComp (Transcript E p) := do
  let r ← runCoordinates E (p+10)
  let middle := prover (coordinateMessages r) 1 0
  runAfterHeader E prover (coordinateMessages r ++ [[middle]]) (header r middle)

/-- A completed sampled header concatenates the initial coordinates, layers, and openings. -/
theorem completed_header_messages {E : Type} [Zero E] {p : Nat}
    (r : Fin (p+10) → E) (middle : E) (ts : Fin 12 → LayerTranscript E p) (o : OpeningTranscript E) :
    transcriptMessages {header r middle with layers := ts, openings := o} =
      coordinateMessages r ++ [[middle]] ++ sequenceMessages ts ++ openingMessages o := by
  have h := congrArg (fun messages : List (List E) =>
    messages ++ [[middle]] ++ sequenceMessages ts ++ openingMessages o) (header_messages r middle)
  simp only [transcriptMessages,sequenceMessages,openingMessages,inputOpeningMessages,List.append_assoc] at h ⊢
  convert h using 1; rfl

/-- Typed full execution and the original wire execution have exactly the same message distribution. -/
theorem runProtocol_encoding {E : Type} [Fintype E] [Nonempty E] [Zero E] (p : Nat) (prover : Prover E) :
    transcriptMessages <$> runProtocol E p prover = runWire E prover (steps p) [] := by
  have hs : steps p = (startKinds p).map WireStep.challenge ++ [.message 1] ++
      (List.range 12).flatMap (layerSteps p) ++
      (roundSteps 6 1 .outputSlot ++ [.message 1] ++ roundSteps 4 1 .inputLow ++
        roundSteps 6 1 .inputSlot ++ [.message 64]) := by
    simp only [steps,startKinds,List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil,List.append_assoc]
  have hl (history : List (List E)) : runWire E prover ((List.range 12).flatMap (layerSteps p)) history =
      sequenceMessages <$> runLayerSequence E p prover 12 history := by
    simpa only [Nat.zero_add] using (runLayerSequence_encoding p 12 0 prover history).symm
  rw [hs]
  simp only [List.append_assoc]
  rw [runWire_append,runWire_onlyChallenges,startKinds_length]
  simp only [runProtocol,map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind,List.nil_append]
  congr 1
  funext r
  simp only [List.cons_append,List.nil_append]
  rw [runWire]
  rw [runWire_append,hl]
  have ho := runOpenings_encoding (E := E) prover
  simp only [List.append_assoc,List.cons_append,List.nil_append] at ho
  simp_rw [← ho]
  simp only [runAfterHeader,map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind,
    completed_header_messages,List.append_assoc,List.cons_append,List.nil_append,ofFn_one]

end CompStark.Keccak.Gkr
