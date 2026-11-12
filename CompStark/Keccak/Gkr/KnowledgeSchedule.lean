/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.KnowledgeBoundaries

/-! # Semantic annotations of every authored GKR wire move -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
namespace CompStark.Keccak.Gkr

/-- Forgetting sumcheck semantic cuts recovers its public wire steps. -/
theorem roundNodes_steps (count degree : Nat) (kind : Nat → Challenge) (cut : Nat → Cut) :
    (roundNodes count degree kind cut).map Prod.fst = roundSteps count degree kind := by
  simp only [roundNodes, roundSteps, List.map_flatMap, List.map_cons, List.map_nil]

/-- Forgetting layer semantic cuts recovers its public wire steps. -/
theorem layerNodes_steps (p : Nat) (d : Fin 12) :
    (layerNodes p d).map Prod.fst = layerSteps p d.val := by
  simp only [layerNodes, layerSteps, List.map_append, List.map_cons, List.map_nil, roundNodes_steps]

/-- Forgetting semantic cuts recovers the concrete GKR schedule. -/
theorem scheduleNodes_steps (p : Nat) : (scheduleNodes p).map Prod.fst = steps p := by
  simp only [scheduleNodes, steps, List.map_append, List.map_map, List.map_cons, List.map_nil,
    List.map_flatten, List.map_ofFn, Function.comp_def, layerNodes_steps, roundNodes_steps]
  congr 2

/-- Adjacent semantic cuts implement the appropriate deterministic boundary at every message. -/
def MessageBoundaryChain (p : Nat) : List (WireStep × Cut) → Prop
  | [] => True
  | (step, c) :: rest =>
      (match step with
        | .message _ => MessageBoundary p c (rest.head?.map Prod.snd)
        | .challenge _ => True) ∧ MessageBoundaryChain p rest

/-- Each sumcheck round has the same residual before its message and challenge. -/
theorem messageBoundaryChain_roundNodes (p count degree : Nat)
    (kind : Nat → Challenge) (cut : Nat → Cut) (tail : List (WireStep × Cut))
    (valid : MessageBoundaryChain p tail) :
    MessageBoundaryChain p (roundNodes count degree kind cut ++ tail) := by
  unfold roundNodes
  induction List.range count with
  | nil => exact valid
  | cons i rest ih =>
    exact ⟨MessageBoundary.same _, trivial, ih⟩

/-- The product and shifted-evaluation message boundaries connect a layer's sumchecks. -/
theorem messageBoundaryChain_layerNodes (p : Nat) (d : Fin 12)
    (tail : List (WireStep × Cut)) (valid : MessageBoundaryChain p tail) :
    MessageBoundaryChain p (layerNodes p d ++ tail) := by
  simp only [layerNodes, List.append_assoc, List.cons_append, List.nil_append]
  refine ⟨MessageBoundary.product _, trivial, ?_⟩
  apply messageBoundaryChain_roundNodes
  apply messageBoundaryChain_roundNodes
  exact ⟨MessageBoundary.evaluations _, trivial, valid⟩

/-- Every layer block preserves the deterministic boundary invariant before its continuation. -/
theorem messageBoundaryChain_layers (p : Nat) (ds : List (Fin 12))
    (tail : List (WireStep × Cut)) (valid : MessageBoundaryChain p tail) :
    MessageBoundaryChain p ((ds.flatMap (layerNodes p)) ++ tail) := by
  induction ds with
  | nil => exact valid
  | cons d ds ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    exact messageBoundaryChain_layerNodes p d _ ih

/-- An initial challenge does not impose a deterministic message boundary. -/
theorem messageBoundaryChain_challenges (p : Nat) (indices : List Nat)
    (kind : Nat → Challenge) (cut : Nat → Cut) (tail : List (WireStep × Cut))
    (valid : MessageBoundaryChain p tail) :
    MessageBoundaryChain p ((indices.map fun i => (.challenge (kind i), cut i)) ++ tail) := by
  induction indices with
  | nil => exact valid
  | cons i rest ih => exact ⟨trivial, ih⟩

/-- The annotated GKR schedule has a valid deterministic boundary at every prover prefix. -/
theorem scheduleNodes_messageBoundaryChain (p : Nat) : MessageBoundaryChain p (scheduleNodes p) := by
  unfold scheduleNodes
  simp only [List.append_assoc]
  apply messageBoundaryChain_challenges
  refine ⟨trivial, ?_⟩
  apply messageBoundaryChain_challenges
  refine ⟨?_, ?_⟩
  · exact MessageBoundary.middle
  · rw [List.flatten_eq_flatMap, List.ofFn_eq_map, List.flatMap_map]
    apply messageBoundaryChain_layers
    apply messageBoundaryChain_roundNodes
    refine ⟨MessageBoundary.word, ?_⟩
    apply messageBoundaryChain_roundNodes
    apply messageBoundaryChain_roundNodes
    exact ⟨MessageBoundary.slices, trivial⟩

/-- The first move samples the first instance coordinate before any prover message. -/
theorem scheduleNodes_first (p : Nat) :
    ∃ rest, scheduleNodes p = (.challenge (.initialInstance 0), .start 0) :: rest := by
  simp only [scheduleNodes, show p+4 = (p+3)+1 from rfl, List.range_succ_eq_map,
    List.map_cons, List.cons_append]
  exact ⟨_, rfl⟩

/-- Forgetting sumcheck wire moves recovers the repeated residual cuts. -/
theorem roundNodes_cuts (count degree : Nat) (kind : Nat → Challenge) (cut : Nat → Cut) :
    (roundNodes count degree kind cut).map Prod.snd = roundCuts count cut := by
  simp only [roundNodes, roundCuts, List.map_flatMap, List.map_cons, List.map_nil]

/-- Consecutive sumcheck blocks have the same cuts as their combined coordinate block. -/
theorem roundCuts_add (a b : Nat) (cut : Nat → Cut) :
    roundCuts (a+b) cut = roundCuts a cut ++ roundCuts b (fun i => cut (a+i)) := by
  simp only [roundCuts, List.range_add, List.flatMap_append, List.flatMap_map]

/-- The semantic annotations give the initial coordinates in their flattened order. -/
theorem initialCuts_blocks (p : Nat) :
    (List.range (p+10)).map Cut.start =
      (List.range (p+4)).map Cut.start ++ [.start (p+4)] ++
        (List.range 5).map (fun i => .start (p+5+i)) := by
  rw [show p+10 = (p+4)+6 by omega, List.range_add, List.map_append, List.map_map,
    show 6 = 5+1 by decide, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Function.comp_def, List.singleton_append,
    List.append_assoc]
  congr 3

/-- Annotating wire moves preserves the mathematical cut sequence of the GKR reduction. -/
theorem cuts_eq (p : Nat) :
    cuts p = (List.range (p+10)).map .start ++ [.start (p+10)] ++
      (List.ofFn fun d : Fin 12 =>
        [.layer d, .product d] ++ roundCuts (p+1) (.pack d) ++ roundCuts 11 (.position d) ++
          [.position d 11, .batch d]).flatten ++
      roundCuts 6 .word ++ [.wordEnd] ++ roundCuts 10 .input ++ [.inputEnd] := by
  simp only [cuts, scheduleNodes, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.map_flatten, List.map_ofFn, Function.comp_def, layerNodes, roundNodes_cuts]
  rw [initialCuts_blocks, show 10 = 4+6 by decide, roundCuts_add]
  simp only [List.append_assoc]

end CompStark.Keccak.Gkr
